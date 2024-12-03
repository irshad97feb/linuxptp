/**
 * @file phc2sys.c
 * @brief Utility program to synchronize two clocks via a PPS.
 * @note Copyright (C) 2012 Richard Cochran <richardcochran@gmail.com>
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License along
 * with this program; if not, write to the Free Software Foundation, Inc.,
 * 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA.
 */
#include <errno.h>
#include <fcntl.h>
#include <float.h>
#include <inttypes.h>
#include <limits.h>
#include <net/if.h>
#include <poll.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/ioctl.h>
#include <sys/queue.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <unistd.h>

#include <linux/pps.h>
#include <linux/ptp_clock.h>

#include "clockadj.h"
#include "clockcheck.h"
#include "contain.h"
#include "ds.h"
#include "fsm.h"
#include "missing.h"
#include "notification.h"
#include "ntpshm.h"
#include "phc.h"
#include "pi.h"
#include "pmc_agent.h"
#include "print.h"
#include "servo.h"
#include "sk.h"
#include "stats.h"
#include "sysoff.h"
#include "tlv.h"
#include "uds.h"
#include "util.h"
#include "version.h"

#define KP 0.7
#define KI 0.3
#define NS_PER_SEC 1000000000LL

#define PHC_PPS_OFFSET_LIMIT 10000000

#define FORCED_SOURCE_CLOCK_PRIORITY 254
#define MAX_SRC_CLOCKS 128
#define HA_SCK_N_FD 1
#define HA_SCK_BUFFER_SIZE 1024
#define HA_SCK_FILEMODE (S_IRUSR|S_IWUSR|S_IRGRP|S_IWGRP) /*0660*/

#define PORT_INDEX_TO_PORT_ID(port, index) (((((unsigned int) port) & 0xFF) << 8) | (((unsigned int) index) & 0xFF))
#define PORT_ID_TO_PORT(id) ((((unsigned int) id) >> 8) & 0xFF)
#define PORT_ID_TO_INDEX(id) (((unsigned int) id) & 0xFF)

struct clock {
	LIST_ENTRY(clock) list;
	LIST_ENTRY(clock) dst_list;
	LIST_ENTRY(clock) ha_list;
	clockid_t clkid;
	int phc_index;
	int sysoff_method;
	int is_utc;
	int dest_only;
	int state;
	int new_state;
	int sync_offset;
	int leap_set;
	int utc_offset_set;
	struct servo *servo;
	enum servo_state servo_state;
	char *device;
	const char *source_label;
	struct stats *offset_stats;
	struct stats *freq_stats;
	struct stats *delay_stats;
	struct clockcheck *sanity_check;
	struct pmc_agent *node;
	int ha_priority;
	int enabled;
};
typedef LIST_HEAD(head, clock) clock_list_head_t;

struct port {
	LIST_ENTRY(port) list;
	unsigned int number;
	int state;
	struct clock *clock;
};

struct phc2sys_private {
	unsigned int stats_max_count;
	int sanity_freq_limit;
	enum servo_type servo_type;
	int phc_readings;
	double phc_interval;
	int forced_sync_offset;
	int kernel_leap;
	int state_changed;
	int clock_state_changed;
	LIST_HEAD(pmc_agent_head, pmc_agent) pmc_agents;
	LIST_HEAD(port_head, port) ports;
	LIST_HEAD(clock_head, clock) clocks;
	LIST_HEAD(dst_clock_head, clock) dst_clocks;
	struct clock *master;
	struct clock *better;
	struct timespec stability_timer;
	int default_sync;
	int forced_source_clock;
	int ha_socket_fd;
};

static struct config *phc2sys_config;

static int clock_handle_leap(struct phc2sys_private *priv,
			     struct clock *clock,
			     int64_t offset, uint64_t ts);

static int normalize_state(int state);

static struct servo *servo_add(struct phc2sys_private *priv,
			       struct clock *clock)
{
	double ppb;
	int max_ppb;
	struct servo *servo;

	clockadj_init(clock->clkid);
	ppb = clockadj_get_freq(clock->clkid);
	/* The reading may silently fail and return 0, reset the frequency to
	   make sure ppb is the actual frequency of the clock. */
	clockadj_set_freq(clock->clkid, ppb);
	if (clock->clkid == CLOCK_REALTIME) {
		sysclk_set_leap(0);
		max_ppb = sysclk_max_freq();
	} else {
		max_ppb = phc_max_adj(clock->clkid);
		if (!max_ppb) {
			pr_err("clock is not adjustable");
			return NULL;
		}
	}

	servo = servo_create(phc2sys_config, priv->servo_type,
			     -ppb, max_ppb, 0);
	if (!servo) {
		pr_err("Failed to create servo");
		return NULL;
	}

	servo_sync_interval(servo, priv->phc_interval);

	return servo;
}

static struct clock *clock_add(struct phc2sys_private *priv, char *device)
{
	struct clock *c;
	clockid_t clkid = CLOCK_INVALID;
	int phc_index = -1;

	if (device) {
		clkid = posix_clock_open(device, &phc_index);
		if (clkid == CLOCK_INVALID)
			return NULL;
	}

	c = calloc(1, sizeof(*c));
	if (!c) {
		pr_err("failed to allocate memory for a clock");
		return NULL;
	}
	c->clkid = clkid;
	c->phc_index = phc_index;
	c->servo_state = SERVO_UNLOCKED;
	c->device = device ? strdup(device) : NULL;

	if (c->clkid == CLOCK_REALTIME) {
		c->source_label = "sys";
		c->is_utc = 1;
	} else {
		c->source_label = "phc";
	}

	if (priv->stats_max_count > 0) {
		c->offset_stats = stats_create();
		c->freq_stats = stats_create();
		c->delay_stats = stats_create();
		if (!c->offset_stats ||
		    !c->freq_stats ||
		    !c->delay_stats) {
			pr_err("failed to create stats");
			return NULL;
		}
	}
	if (priv->sanity_freq_limit) {
		c->sanity_check = clockcheck_create(priv->sanity_freq_limit);
		if (!c->sanity_check) {
			pr_err("failed to create clock check");
			return NULL;
		}
	}

	if (clkid != CLOCK_INVALID)
		c->servo = servo_add(priv, c);

	if (clkid != CLOCK_INVALID && clkid != CLOCK_REALTIME)
		c->sysoff_method = sysoff_probe(CLOCKID_TO_FD(clkid),
						priv->phc_readings);

	c->enabled = 1;

	LIST_INSERT_HEAD(&priv->clocks, c, list);
	return c;
}

static void clock_cleanup(struct phc2sys_private *priv)
{
	struct clock *c, *tmp;

	LIST_FOREACH_SAFE(c, &priv->clocks, list, tmp) {
		if (c->servo) {
			servo_destroy(c->servo);
		}
		if (c->sanity_check) {
			clockcheck_destroy(c->sanity_check);
		}
		if (c->delay_stats) {
			stats_destroy(c->delay_stats);
		}
		if (c->freq_stats) {
			stats_destroy(c->freq_stats);
		}
		if (c->offset_stats) {
			stats_destroy(c->offset_stats);
		}
		if (c->device) {
			free(c->device);
		}
		free(c);
	}
}

static struct clock * clock_get_by_device(struct phc2sys_private *priv,
	const char * device)
{
	struct clock * clock = NULL;
	LIST_FOREACH(clock, &priv->clocks, list) {
		/* ignore the dst clock */
		if (clock->state == PS_MASTER)
			continue;

		/* sanity check */
		if (!clock->device)
			continue;

		if (strcmp(device, clock->device) == 0)
			break;
	}
	return clock;
}

static size_t clock_count_enabled_sources(struct phc2sys_private *priv,
	struct clock *ignore)
{
	size_t count = 0;
	struct clock * clock = NULL;

	LIST_FOREACH(clock, &priv->clocks, list) {
		/* ignore the dst clock */
		if (clock->state == PS_MASTER)
			continue;

		if (clock == ignore)
			continue;

		if (!clock->enabled)
			continue;

		count++;
	}
	return count;
}

static bool clock_match_ha_dds_requirements(struct clock *clock, struct config *cfg)
{
	/* get requirements */
	int local_clock_class, max_local_clock_class = config_get_int(cfg, NULL, "ha_max_local_clockClass");
	unsigned int clock_accuracy, max_clock_accuracy = config_get_int(cfg, NULL, "ha_max_local_clockAccuracy");
	unsigned int offset, max_offset_scaled_log_variance = config_get_int(cfg, NULL, "ha_max_local_offsetScaledLogVar");

	/* sanity check */
	if (clock->node == NULL) {
		pr_debug("clock %s node is (null)", clock->device);
		return false;
	}

	if (!clock->node->dds_valid) {
		pr_debug("clock %s dds is invalid", clock->device);
		return false;
	}

	/* max local clock class (lower is better) */
	local_clock_class = clock->node->dds.clockQuality.clockClass;
	if (local_clock_class > max_local_clock_class) {
		pr_debug("clock %s local clock class %d > max local clock class %d",
			clock->device, local_clock_class, max_local_clock_class);
		return false;
	}

	/* max clock accuracy (lower is better) */
	clock_accuracy = clock->node->dds.clockQuality.clockAccuracy;
	if (clock_accuracy > max_clock_accuracy) {
		pr_debug("clock %s clock accuracy %d > max clock accuracy %d",
			clock->device, clock_accuracy, max_clock_accuracy);
		return false;
	}

	/* max offset scaled log variance (lower is better) */
	offset = clock->node->dds.clockQuality.offsetScaledLogVariance;
	if (offset > max_offset_scaled_log_variance) {
		pr_debug("clock %s offset scaled log variance 0x%x > max offset 0x%x",
			clock->device, offset, max_offset_scaled_log_variance);
		return false;
	}

	return true;
}

static bool clock_match_ha_tpds_requirements(struct clock *clock, struct config *cfg)
{
	/* get requirements */
	bool check_time_traceable = config_get_int(cfg, NULL, "ha_gm_timeTraceable");
	bool check_freq_traceable = config_get_int(cfg, NULL, "ha_gm_frequencyTraceable");

	/* sanity check */
	if (clock->node == NULL) {
		pr_debug("clock %s node is (null)", clock->device);
		return false;
	}

	/* is time traceable */
	if (check_time_traceable && !clock->node->time_traceable) {
		pr_debug("clock %s time is not traceable", clock->device);
		return false;
	}

	/* is frequency traceable */
	if (check_freq_traceable && !clock->node->freq_traceable) {
		pr_debug("clock %s frequency is not traceable", clock->device);
		return false;
	}

	return true;
}

static bool clock_match_ha_pds_requirements(struct clock *clock, struct config *cfg)
{
	/* get requirements */
	int gm_clock_class, max_gm_clock_class = config_get_int(cfg, NULL, "ha_max_gm_clockClass");
	unsigned int clock_accuracy, max_clock_accuracy = config_get_int(cfg, NULL, "ha_max_gm_clockAccuracy");
	unsigned int offset, max_offset_scaled_log_variance = config_get_int(cfg, NULL, "ha_max_gm_offsetScaledLogVar");

	/* sanity check */
	if (clock->node == NULL) {
		pr_debug("clock %s node is (null)", clock->device);
		return false;
	}

	if (!clock->node->pds_valid) {
		pr_debug("clock %s pds is invalid", clock->device);
		return false;
	}

	/* max gm clock class (lower is better) */
	gm_clock_class = clock->node->pds.grandmasterClockQuality.clockClass;
	if (gm_clock_class > max_gm_clock_class) {
		pr_debug("clock %s GM clock class %d > max clock class %d",
			clock->device, gm_clock_class, max_gm_clock_class);
		return false;
	}

	/* max clock accuracy (lower is better) */
	clock_accuracy = clock->node->pds.grandmasterClockQuality.clockAccuracy;
	if (clock_accuracy > max_clock_accuracy) {
		pr_debug("clock %s GM clock accuracy %d > max clock accuracy %d",
			clock->device, clock_accuracy, max_clock_accuracy);
		return false;
	}

	/* max offset scaled log variance (lower is better) */
	offset = clock->node->pds.grandmasterClockQuality.offsetScaledLogVariance;
	if (offset > max_offset_scaled_log_variance) {
		pr_debug("clock %s GM offset scaled log variance 0x%x > max offset 0x%x",
			clock->device, offset, max_offset_scaled_log_variance);
		return false;
	}

	return true;
}

static bool clock_match_ha_requirements(struct clock *clock, struct config *cfg)
{
	return clock_match_ha_dds_requirements(clock, cfg) &&
		clock_match_ha_tpds_requirements(clock, cfg) &&
		clock_match_ha_pds_requirements(clock, cfg);
}

/* save a list of available source clocks that matches ha requirements */
static int clock_available_ha_src_clocks(struct phc2sys_private *priv, struct config *cfg, clock_list_head_t *available_clocks)
{
	int err, retries;
	struct clock *clock;
	bool check_time_traceable, check_freq_traceable;

	LIST_INIT(available_clocks);

	check_time_traceable = config_get_int(cfg, NULL, "ha_gm_timeTraceable");
	check_freq_traceable = config_get_int(cfg, NULL, "ha_gm_frequencyTraceable");

	LIST_FOREACH(clock, &priv->clocks, list) {
		pr_debug("clock %s state %d", clock->device, clock->state);

		/* ignore the dst clock */
		if (clock->state == PS_MASTER) {
			pr_debug("clock %s discarded because state is PS_MASTER", clock->device);
			continue;
		}

		/* sanity check */
		if (clock->node == NULL) {
			pr_debug("clock %s discarded because node is (null)", clock->device);
			continue;
		}

		if (!clock->enabled) {
			pr_debug("clock %s is disabled", clock->device);
			continue;
		}

		/* get Default Data Set */
		if (!clock->node->dds_valid) {
			retries = 0;
			while(retries < 10) {
				if (!is_running()) {
					return -1;
				}
				err = pmc_agent_query_dds(clock->node, 1000);
				if (!err) {
					break;
				}
				if (err == -ETIMEDOUT) {
					pr_notice("Waiting for ptp4l...");
					retries++;
				} else {
					return -1;
				}
			}

			if (err != 0) {
				pr_debug("clock %s discarded because tds is invalid", clock->device);
				continue;
			}
		}

		if (!clock_match_ha_dds_requirements(clock, cfg))
			continue;

		if (check_time_traceable || check_freq_traceable) {
			/* get Time Properties Data Set */
			retries = 0;
			while(retries < 10) {
				if (!is_running()) {
					return -1;
				}
				err = pmc_agent_query_utc_offset(clock->node, 1000);
				if (!err) {
					break;
				}
				if (err == -ETIMEDOUT) {
					pr_notice("Waiting for ptp4l...");
					retries++;
				} else {
					return -1;
				}
			}

			if (err != 0) {
				pr_debug("clock %s discarded because tds is invalid", clock->device);
				continue;
			}

			if (!clock_match_ha_tpds_requirements(clock, cfg))
				continue;
		}

		/* get Parent Data Set */
		if (!clock->node->pds_valid) {
			retries = 0;
			while (retries < 10) {
				if (!is_running()) {
					return -1;
				}
				err = pmc_agent_query_pds(clock->node, 1000);
				if (!err) {
					break;
				}
				if (err == -ETIMEDOUT) {
					pr_notice("Waiting for ptp4l...");
					retries++;
				} else {
					return -1;
				}
			}

			if (err != 0) {
				pr_debug("clock %s discarded because pds is invalid", clock->device);
				continue;
			}
		}

		if (!clock_match_ha_pds_requirements(clock, cfg))
			continue;

		clock->ha_list.le_next = NULL;
		clock->ha_list.le_prev = NULL;
		LIST_INSERT_HEAD(available_clocks, clock, ha_list);
	}

	return 0;
}

static void port_cleanup(struct phc2sys_private *priv)
{
	struct port *p, *tmp;

	LIST_FOREACH_SAFE(p, &priv->ports, list, tmp) {
		free(p);
	}
}

static struct port *port_get(struct phc2sys_private *priv, unsigned int number)
{
	struct port *p;

	LIST_FOREACH(p, &priv->ports, list) {
		if (p->number == number)
			return p;
	}
	return NULL;
}

static struct port *port_add(struct phc2sys_private *priv, unsigned int number,
			     char *device)
{
	struct port *p;
	struct clock *c = NULL, *tmp;

	p = port_get(priv, number);
	if (p)
		return p;
	/* port is a new one, look whether we have the device already on
	 * a different port */
	LIST_FOREACH(tmp, &priv->clocks, list) {
		if (!strcmp(tmp->device, device)) {
			c = tmp;
			break;
		}
	}
	if (!c) {
		c = clock_add(priv, device);
		if (!c)
			return NULL;
	}
	p = malloc(sizeof(*p));
	if (!p) {
		pr_err("failed to allocate memory for a port");
		return NULL;
	}
	p->number = number;
	p->clock = c;
	LIST_INSERT_HEAD(&priv->ports, p, list);
	return p;
}

static struct pmc_agent *pmc_agent_get(struct phc2sys_private *priv, unsigned int index)
{
	struct pmc_agent *node;
	LIST_FOREACH(node, &priv->pmc_agents, list) {
		if (node->index == index) {
			break;
		}
	}
	return node;
}

static struct pmc_agent *pmc_agent_add(struct phc2sys_private *priv, unsigned int index)
{
	struct pmc_agent *node = pmc_agent_get(priv, index);
	if (node)
		return node;

	node = pmc_agent_create();
	if (!node) {
		pr_err("failed to allocate memory for a pmc agent");
		return NULL;
	}

	node->index = index;
	LIST_INSERT_HEAD(&priv->pmc_agents, node, list);
	return node;
}

static void pmc_agent_cleanup(struct phc2sys_private *priv)
{
	struct pmc_agent *node, *tmp;
	LIST_FOREACH_SAFE(node, &priv->pmc_agents, list, tmp) {
		pmc_agent_destroy(node);
	}
}

static void clock_reinit(struct phc2sys_private *priv, struct clock *clock,
			 int new_state)
{
	int err = -1, phc_index = -1, phc_switched = 0, state, timestamping;
	struct port *p;
	struct servo *servo;
	struct sk_ts_info ts_info;
	char iface[IFNAMSIZ];
	clockid_t clkid = CLOCK_INVALID;
	struct pmc_agent *node;
	unsigned int pmc_index;

	LIST_FOREACH(p, &priv->ports, list) {
		if (p->clock != clock) {
			continue;
		}

		pmc_index = PORT_ID_TO_INDEX(p->number);
		node = pmc_agent_get(priv, pmc_index);
		if (!node) {
			pr_warning("pmc node associated to port number %d not found", p->number);
			continue;
		}
		err = pmc_agent_query_port_properties(node, 1000,
						      p->number, &state,
						      &timestamping, iface);
		if (!err) {
			p->state = normalize_state(state);
		}
		break;
	}

	if (!err && timestamping != TS_SOFTWARE) {
		/* Check if device changed */
		if (strcmp(clock->device, iface)) {
			free(clock->device);
			clock->device = strdup(iface);
		}
		/* Check if phc index changed */
		if (!sk_get_ts_info(clock->device, &ts_info) &&
		    clock->phc_index != ts_info.phc_index) {
			clkid = posix_clock_open(clock->device, &phc_index);
			if (clkid == CLOCK_INVALID)
				return;

			posix_clock_close(clock->clkid);
			clock->clkid = clkid;
			clock->phc_index = phc_index;

			servo = servo_add(priv, clock);
			if (servo) {
				servo_destroy(clock->servo);
				clock->servo = servo;
			}

			phc_switched = 1;
		}
	}

	if (new_state == PS_MASTER || phc_switched) {
		servo_reset(clock->servo);
		clock->servo_state = SERVO_UNLOCKED;

		if (clock->offset_stats) {
			stats_reset(clock->offset_stats);
			stats_reset(clock->freq_stats);
			stats_reset(clock->delay_stats);
		}
	}
}

static struct clock *find_dst_clock(struct phc2sys_private *priv,
				    int phc_index)
{
	struct clock *c = NULL;
	LIST_FOREACH(c, &priv->dst_clocks, dst_list) {
		if (c->phc_index == phc_index) {
			break;
		}
	}
	return c;
}

static void reconfigure(struct phc2sys_private *priv)
{
	struct clock *c, *rt = NULL, *src = NULL, *last = NULL, *dup = NULL;
	int src_cnt = 0, dst_cnt = 0;

	pr_info("reconfiguring after port state change");
	priv->state_changed = 0;

	while (priv->dst_clocks.lh_first != NULL) {
		LIST_REMOVE(priv->dst_clocks.lh_first, dst_list);
	}

	LIST_FOREACH(c, &priv->clocks, list) {
		if (c->clkid == CLOCK_REALTIME) {
			rt = c;
			continue;
		}

		if (c->new_state) {
			clock_reinit(priv, c, c->new_state);
			c->state = c->new_state;
			c->new_state = 0;
		}

		switch (c->state) {
		case PS_FAULTY:
		case PS_DISABLED:
		case PS_LISTENING:
		case PS_PRE_MASTER:
		case PS_MASTER:
		case PS_PASSIVE:
			dup = find_dst_clock(priv, c->phc_index);
			if (!dup) {
				pr_info("selecting %s for synchronization",
					c->device);
				dst_cnt++;
				LIST_INSERT_HEAD(&priv->dst_clocks,
						 c, dst_list);
			} else {
				pr_info("skipping %s: %s has the same clock "
					"and is already selected",
					c->device, dup->device);
			}
			break;
		case PS_UNCALIBRATED:
			src_cnt++;
			break;
		case PS_SLAVE:
			src = c;
			src_cnt++;
			break;
		}
		last = c;
	}
	if (dst_cnt > 1 && !src && priv->default_sync) {
		if (!rt || rt->dest_only) {
			priv->master = last;
			/* Reset to original state in next reconfiguration. */
			priv->master->new_state = priv->master->state;
			priv->master->state = PS_SLAVE;
			if (rt)
				rt->state = PS_SLAVE;
			pr_info("no source, selecting %s as the default clock",
				last->device);
			return;
		}
	}
	if (src_cnt > 1) {
		pr_info("multiple master clocks available, postponing sync...");
		priv->master = NULL;
		return;
	}
	if (src_cnt > 0 && !src) {
		pr_info("master clock not ready, waiting...");
		priv->master = NULL;
		return;
	}
	if (!src_cnt && !dst_cnt) {
		pr_info("no PHC ready, waiting...");
		priv->master = NULL;
		return;
	}
	if ((!src_cnt && (!rt || rt->dest_only)) ||
	    (!dst_cnt && !rt)) {
		pr_info("nothing to synchronize");
		priv->master = NULL;
		return;
	}
	if (!src_cnt) {
		src = rt;
		rt->state = PS_SLAVE;
	} else if (rt) {
		if (rt->state != PS_MASTER) {
			rt->state = PS_MASTER;
			clock_reinit(priv, rt, rt->state);
		}
		LIST_INSERT_HEAD(&priv->dst_clocks, rt, dst_list);
		pr_info("selecting %s for synchronization", rt->device);
	}
	priv->master = src;
	pr_info("selecting %s as the master clock", src->device);
}

static int read_phc(clockid_t clkid, clockid_t sysclk, int readings,
		    int64_t *offset, uint64_t *ts, int64_t *delay)
{
	struct timespec tdst1, tdst2, tsrc;
	int i;
	int64_t interval, best_interval = INT64_MAX;

	/* Pick the quickest clkid reading. */
	for (i = 0; i < readings; i++) {
		if (clock_gettime(sysclk, &tdst1) ||
				clock_gettime(clkid, &tsrc) ||
				clock_gettime(sysclk, &tdst2)) {
			pr_err("failed to read clock: %m");
			return 0;
		}

		interval = (tdst2.tv_sec - tdst1.tv_sec) * NS_PER_SEC +
			tdst2.tv_nsec - tdst1.tv_nsec;

		if (best_interval > interval) {
			best_interval = interval;
			*offset = (tdst1.tv_sec - tsrc.tv_sec) * NS_PER_SEC +
				tdst1.tv_nsec - tsrc.tv_nsec + interval / 2;
			*ts = tdst2.tv_sec * NS_PER_SEC + tdst2.tv_nsec;
		}
	}
	*delay = best_interval;

	return 1;
}

static int64_t get_sync_offset(struct phc2sys_private *priv, struct clock *dst)
{
	int direction = priv->forced_sync_offset;

	if (!direction)
		direction = dst->is_utc - priv->master->is_utc;
	return (int64_t)dst->sync_offset * NS_PER_SEC * direction;
}

static void update_clock_stats(struct clock *clock, unsigned int max_count,
			       int64_t offset, double freq, int64_t delay)
{
	struct stats_result offset_stats, freq_stats, delay_stats;

	stats_add_value(clock->offset_stats, offset);
	stats_add_value(clock->freq_stats, freq);
	if (delay >= 0)
		stats_add_value(clock->delay_stats, delay);

	if (stats_get_num_values(clock->offset_stats) < max_count)
		return;

	stats_get_result(clock->offset_stats, &offset_stats);
	stats_get_result(clock->freq_stats, &freq_stats);

	if (!stats_get_result(clock->delay_stats, &delay_stats)) {
		pr_info("%s "
			"rms %4.0f max %4.0f "
			"freq %+6.0f +/- %3.0f "
			"delay %5.0f +/- %3.0f",
			clock->device,
			offset_stats.rms, offset_stats.max_abs,
			freq_stats.mean, freq_stats.stddev,
			delay_stats.mean, delay_stats.stddev);
	} else {
		pr_info("%s "
			"rms %4.0f max %4.0f "
			"freq %+6.0f +/- %3.0f",
			clock->device,
			offset_stats.rms, offset_stats.max_abs,
			freq_stats.mean, freq_stats.stddev);
	}

	stats_reset(clock->offset_stats);
	stats_reset(clock->freq_stats);
	stats_reset(clock->delay_stats);
}

static void update_clock(struct phc2sys_private *priv, struct clock *clock,
			 int64_t offset, uint64_t ts, int64_t delay)
{
	enum servo_state state;
	double ppb;

	if (clock_handle_leap(priv, clock, offset, ts))
		return;

	offset += get_sync_offset(priv, clock);

	if (clock->sanity_check && clockcheck_sample(clock->sanity_check, ts))
		servo_reset(clock->servo);

	ppb = servo_sample(clock->servo, offset, ts, 1.0, &state);
	clock->servo_state = state;

	switch (state) {
	case SERVO_UNLOCKED:
		break;
	case SERVO_JUMP:
		clockadj_step(clock->clkid, -offset);
		if (clock->sanity_check)
			clockcheck_step(clock->sanity_check, -offset);
		/* Fall through. */
	case SERVO_LOCKED:
	case SERVO_LOCKED_STABLE:
		clockadj_set_freq(clock->clkid, -ppb);
		if (clock->clkid == CLOCK_REALTIME)
			sysclk_set_sync();
		if (clock->sanity_check)
			clockcheck_set_freq(clock->sanity_check, -ppb);
		break;
	}

	if (clock->offset_stats) {
		update_clock_stats(clock, priv->stats_max_count, offset, ppb, delay);
	} else {
		if (delay >= 0) {
			pr_info("%s %s offset %9" PRId64 " s%d freq %+7.0f "
				"delay %6" PRId64,
				clock->device, priv->master->source_label,
				offset, state, ppb, delay);
		} else {
			pr_info("%s %s offset %9" PRId64 " s%d freq %+7.0f",
				clock->device, priv->master->source_label,
				offset, state, ppb);
		}
	}
}

static void enable_pps_output(clockid_t src)
{
	int enable = 1;

	if (!phc_has_pps(src))
		return;
	if (ioctl(CLOCKID_TO_FD(src), PTP_ENABLE_PPS, enable) < 0)
		pr_warning("failed to enable PPS output");
}

static int read_pps(int fd, int64_t *offset, uint64_t *ts)
{
	struct pps_fdata pfd;

	pfd.timeout.sec = 10;
	pfd.timeout.nsec = 0;
	pfd.timeout.flags = ~PPS_TIME_INVALID;
	if (ioctl(fd, PPS_FETCH, &pfd)) {
		pr_err("failed to fetch PPS: %m");
		return 0;
	}

	*ts = pfd.info.assert_tu.sec * NS_PER_SEC;
	*ts += pfd.info.assert_tu.nsec;

	*offset = *ts % NS_PER_SEC;
	if (*offset > NS_PER_SEC / 2)
		*offset -= NS_PER_SEC;

	return 1;
}

static int do_pps_loop(struct phc2sys_private *priv, struct clock *clock,
		       int fd)
{
	int64_t pps_offset, phc_offset, phc_delay;
	uint64_t pps_ts, phc_ts;
	clockid_t src = priv->master->clkid;
	struct pmc_agent *node = LIST_FIRST(&priv->pmc_agents);

	priv->master->source_label = "pps";

	if (src == CLOCK_INVALID) {
		/* The sync offset can't be applied with PPS alone. */
		pmc_agent_set_sync_offset(node, 0);
	} else {
		enable_pps_output(priv->master->clkid);
	}

	while (is_running()) {
		if (!read_pps(fd, &pps_offset, &pps_ts)) {
			continue;
		}

		/* If a PHC is available, use it to get the whole number
		   of seconds in the offset and PPS for the rest. */
		if (src != CLOCK_INVALID) {
			if (!read_phc(src, clock->clkid, priv->phc_readings,
				      &phc_offset, &phc_ts, &phc_delay))
				return -1;

			/* Convert the time stamp to the PHC time. */
			phc_ts -= phc_offset;

			/* Check if it is close to the start of the second. */
			if (phc_ts % NS_PER_SEC > PHC_PPS_OFFSET_LIMIT) {
				pr_warning("PPS is not in sync with PHC"
					   " (0.%09lld)", phc_ts % NS_PER_SEC);
				continue;
			}

			phc_ts = phc_ts / NS_PER_SEC * NS_PER_SEC;
			pps_offset = pps_ts - phc_ts;
		}

		if (pmc_agent_update(node) < 0)
			continue;
		update_clock(priv, clock, pps_offset, pps_ts, -1);
	}
	close(fd);
	return 0;
}

static int update_needed(struct clock *c)
{
	switch (c->state) {
	case PS_FAULTY:
	case PS_DISABLED:
	case PS_LISTENING:
	case PS_PRE_MASTER:
	case PS_MASTER:
	case PS_PASSIVE:
		return 1;
	case PS_UNCALIBRATED:
	case PS_SLAVE:
		break;
	}
	return 0;
}

/* check configuration if one of the source clocks is force locked to be active */
static struct clock* ha_forced_source_clock(struct phc2sys_private *priv, struct config *cfg)
{
	struct clock *clock = NULL, *best = NULL;

	LIST_FOREACH(clock, &priv->clocks, list) {
		/* ignore the dst clock */
		if (clock->state == PS_MASTER) {
			continue;
		}

		if (FORCED_SOURCE_CLOCK_PRIORITY == clock->ha_priority) {
			pr_info("HA automatic source selection is disabled by configuration");
			priv->forced_source_clock = 1;
			best = clock;
		}
	}

	return best;
}

static struct clock* ha_select_clock(struct phc2sys_private *priv, struct config *cfg)
{
	int highest_priority;
	int clock_class, lowest_clock_class;
	struct clock *clock = NULL, *best = NULL;
	clock_list_head_t ha_available_clocks;

	/* save a list of available source clocks that matches requirements */
	if (clock_available_ha_src_clocks(priv, cfg, &ha_available_clocks) < 0) {
		pr_err("failed to create ha available clock list");
		return NULL;
	}

	/* one or more sources match requirements, select highest priority */
	highest_priority = -1;
	LIST_FOREACH(clock, &ha_available_clocks, ha_list) {/* select highest priority clock
		   more than one clock with same priority, select first
		   don't select clocks with ha_priority 0 */
		if (clock->ha_priority > highest_priority) {
			pr_notice("new highest ha priority clock %s ha_priority %d",
				clock->device, clock->ha_priority);
			best = clock;
			highest_priority = clock->ha_priority;
		}
	}

	/* no sources match requirements, choose best available clockClass */
	if (!best) {
		lowest_clock_class = 256;
		LIST_FOREACH(clock, &priv->clocks, list) {
			/* ignore the dst clock */
			if (clock->state == PS_MASTER)
				continue;

			/* sanity check */
			if (clock->node == NULL)
				continue;

			/* clock disabled */
			if (!clock->enabled)
				continue;

			/* get clock class */
			clock_class = clock->node->dds.clockQuality.clockClass;
			if (clock_class  <= lowest_clock_class) {
				pr_notice("new better clock class clock %s clock class %d",
					clock->device, clock_class);
				best = clock;
				lowest_clock_class = clock_class;
			}
		}
	}

	/* no clock selected, select first clock configured (last in list) */
	if (!best) {
		LIST_FOREACH(clock, &priv->clocks, list) {
			/* ignore the dst clock */
			if (clock->state == PS_MASTER)
				continue;

			/* sanity check */
			if (clock->node == NULL)
				continue;

			/* clock disabled */
			if (!clock->enabled)
				continue;

			best = clock;
		}
	}

	if (best)
		pr_notice("best clock available %s", best->device);

	return best;
}

static struct clock* check_and_select_clock(struct phc2sys_private *priv, struct config *cfg)
{
	struct clock *active = priv->master, *candidate = NULL;
	int stability_timer = 0;
	struct timespec now;

	/* Active source degrades - re-run ha_select_clock algorithm */
	if ((active->node->new_dds && !clock_match_ha_dds_requirements(active, cfg)) ||
	    (active->node->new_tpds && !clock_match_ha_tpds_requirements(active, cfg)) ||
		(active->node->new_pds && !clock_match_ha_pds_requirements(active, cfg))) {

		pr_notice("active clock %s has degraded", active->device);

		active->node->new_dds = false;
		active->node->new_tpds = false;
		active->node->new_pds = false;

		candidate = ha_select_clock(priv, cfg);
		if (active != candidate) {
			pr_notice("new source clock selected %s", candidate->device);
			return candidate;
		}
	}

	/* Primary clock is active, secondary clock becomes better quality */
	/* Secondary clock is active, primary clock becomes better quality */

	/* select best clock available */
	candidate = ha_select_clock(priv, cfg);

	if (active == candidate) {
		/* active source still is or became the best clock available again */
		priv->better = NULL;
		priv->stability_timer.tv_sec = 0;
		priv->stability_timer.tv_nsec = 0;
	} else {
		/* new clock candidate */

		/* candidate has equal priority and clockClass than active - don't change active */
		if ((active->ha_priority == candidate->ha_priority) &&
			clock_match_ha_requirements(active, cfg)) {
			return NULL;
		}

		/* stability timer equal 0 - change active */
		stability_timer = config_get_int(cfg, NULL, "ha_stability_timer");
		if (stability_timer == 0) {
			pr_notice("new source clock selected %s", candidate->device);
			return candidate;
		}

		if (candidate != priv->better) {
			priv->better = candidate;
			/* start/restart stability timer */
			clock_gettime(CLOCK_REALTIME, &now);
			priv->stability_timer.tv_sec = now.tv_sec + stability_timer;
			priv->stability_timer.tv_nsec = now.tv_nsec;
		}
	}

	return NULL;
}

static void reset_new_dataset_flags(struct phc2sys_private *priv)
{
	struct pmc_agent *node;
	LIST_FOREACH(node, &priv->pmc_agents, list) {
		node->new_dds = false;
		node->new_tpds = false;
		node->new_pds = false;
	}
}

static int ha_com_socket_close(int fd)
{
	struct sockaddr_un sa;
	socklen_t len = sizeof(sa);

	if (!getsockname(fd, (struct sockaddr *) &sa, &len) &&
		sa.sun_family == AF_LOCAL) {
		unlink(sa.sun_path);
	}

	shutdown(fd, SHUT_RDWR);
	close(fd);
	return 0;
}

static int ha_com_socket_open(int *fd_out, struct config *cfg)
{
	int fd, err;
	struct sockaddr_un sa;
	const int backlog = 50;
	const char *path = config_get_string(cfg, NULL, "ha_phc2sys_com_socket");

	unlink(path);

	fd = socket(AF_LOCAL, SOCK_STREAM | SOCK_NONBLOCK, 0);
	if (fd < 0) {
		pr_err("ha_com_socket: failed to create socket: %m");
		return -1;
	}

	memset(&sa, 0, sizeof(sa));
	sa.sun_family = AF_LOCAL;
	strncpy(sa.sun_path, path, sizeof(sa.sun_path) - 1);

	err = bind(fd, (struct sockaddr *) &sa, sizeof(sa));
	if (err < 0) {
		pr_err("ha_com_socket: bind failed: %m");
		close(fd);
		return -1;
	}

	err = listen(fd, backlog);
	if (err < 0) {
		pr_err("ha_com_socket: listen failed: %m");
		close(fd);
		return -1;
	}

	*fd_out = fd;
	chmod(path, HA_SCK_FILEMODE);

	return 0;
}

static int ha_com_socket_recv(int fd, void *buf, size_t buflen)
{
	int cnt;

	cnt = read(fd, buf, buflen);
	if (cnt <= 0) {
		pr_err("ha_com_socket: read failed: %m");
		return -errno;
	}

	((char*)buf)[cnt] = '\0';

	return 0;
}

static int ha_com_socket_send(int fd, void *buf, size_t buflen)
{
	int cnt;

	cnt = send(fd, buf, buflen, MSG_NOSIGNAL);
	if (cnt < 0) {
		pr_err("ha_com_socket: send failed: %m");
		return -errno;
	}
	return cnt;
}

static int ha_handle_status_msg(struct phc2sys_private *priv, char *response,
			size_t resplen)
{
	struct clock *clock;
	size_t curlen = 0;

	/* header */
	curlen = snprintf(response, resplen,
		"act   interface   priority   clockClass   clockAcc   offset   time   freq   "
		"gm.clockClass    gm.clockAcc   gm.offset\n\n");

	LIST_FOREACH(clock, &priv->clocks, list) {

		/* ignore the dst clock */
		if (clock->state == PS_MASTER)
			continue;

		/* sanity check */
		if (clock->node == NULL)
			continue;

		curlen += snprintf(response + curlen, resplen - curlen,
			" %c    %9s   %8d   %10d       0x%2x   0x%4x     %s    %s  %13d   "
			"        0x%2x      0x%4x\n",
			(priv->master ==  clock) ? '*' :
				(priv->better == clock) ? '-' :
					(!clock->enabled) ? 'x' : ' ',
			clock->device, clock->ha_priority,
			clock->node->dds.clockQuality.clockClass,
			clock->node->dds.clockQuality.clockAccuracy,
			clock->node->dds.clockQuality.offsetScaledLogVariance,
			clock->node->time_traceable ? "yes" : "no ",
			clock->node->freq_traceable ? "yes" : "no ",
			clock->node->pds.grandmasterClockQuality.clockClass,
			clock->node->pds.grandmasterClockQuality.clockAccuracy,
			clock->node->pds.grandmasterClockQuality.offsetScaledLogVariance);
	}

	curlen += snprintf(response + curlen, resplen - curlen,
		"\n\nSource forced? %s\n", priv->forced_source_clock ? "yes" : "no");

	return curlen;
}

static bool starts_with(const char *prefix, const char *str)
{
	return 0 == strncmp(prefix, str, strlen(prefix) - 1);
}

static char * str_at_column(char *msg, size_t column)
{
	int i;
	char * str = NULL;

	/* split and walk over the columns */
	strtok(msg, " ");
	for (i = 1; i < column; i++) {
		str = strtok(NULL, " ");
	}

	return str;
}

static void ha_set_clock_source(struct phc2sys_private *priv, struct clock *clock)
{
	pr_notice("new clock source selected %s", clock->device);

	priv->master = clock;
	priv->better = NULL;
	priv->stability_timer.tv_sec = 0;
	priv->stability_timer.tv_nsec = 0;
}

static int ha_handle_enable_lock_msg(struct phc2sys_private *priv, char *msg,
			char *response, size_t resplen)
{
	size_t curlen = 0;
	char *interface = NULL;
	struct clock *clock = NULL;

	interface = str_at_column(msg, 3);
	if (strlen(interface) == 0) {
		return snprintf(response, resplen, "Error: Usage 'enable lock <interface>'");
	}

	clock = clock_get_by_device(priv, interface);
	if (!clock) {
		return snprintf(response, resplen, "Error: Interface not found");
	}

	pr_info("HA automatic source selection is disabled by command");
	pr_info("Only interface %s will be used as source clock", clock->device);

	ha_set_clock_source(priv, clock);

	priv->forced_source_clock = 1;

	curlen = snprintf(response, resplen, "Success");

	return curlen;
}

static int ha_handle_disable_lock_msg(struct phc2sys_private *priv,
			struct config *cfg, char *response, size_t resplen)
{
	size_t curlen = 0;
	struct clock *clock = NULL;

	if (priv->forced_source_clock) {
		pr_info("HA automatic source selection is enabled by command");
		/* re-enable HA source selection algorithm */
		priv->forced_source_clock = 0;
		/* select the best clock available */
		clock = ha_select_clock(priv, cfg);
		if (clock && clock != priv->master) {
			ha_set_clock_source(priv, clock);
		}
	}

	curlen = snprintf(response, resplen, "Success");

	return curlen;
}

static int ha_handle_enable_source_msg(struct phc2sys_private *priv,
			struct config *cfg, char *msg, char *response, size_t resplen)
{
	size_t curlen;
	char *interface = NULL;
	struct clock *clock = NULL;

	interface = str_at_column(msg, 3);
	if (strlen(interface) == 0) {
		return snprintf(response, resplen, "Error: Usage 'enable source <interface>'");
	}

	clock = clock_get_by_device(priv, interface);
	if (!clock) {
		return snprintf(response, resplen, "Error: Interface not found");
	}

	clock->enabled = 1;

	if (!priv->forced_source_clock) {
		/* select the best clock available */
		clock = ha_select_clock(priv, cfg);
		if (clock && clock != priv->master) {
			ha_set_clock_source(priv, clock);
		}
	}

	curlen = snprintf(response, resplen, "Success");

	return curlen;
}

static int ha_handle_disable_source_msg(struct phc2sys_private *priv,
			struct config *cfg, char *msg, char *response, size_t resplen)
{
	size_t curlen;
	char *interface = NULL;
	struct clock *clock = NULL;

	interface = str_at_column(msg, 3);
	if (strlen(interface) == 0) {
		return snprintf(response, resplen, "Error: Usage 'disable source <interface>'");
	}

	clock = clock_get_by_device(priv, interface);
	if (!clock) {
		return snprintf(response, resplen, "Error: Interface not found");
	}

	/* check if is the last clock enabled */
	if (clock_count_enabled_sources(priv, clock) == 0) {
		return snprintf(response, resplen, "Error: Last interface enabled");
	}

	clock->enabled = 0;

	/* disabling clock source */
	if (clock == priv->master && !priv->forced_source_clock) {
		/* select the best clock available */
		clock = ha_select_clock(priv, cfg);
		if (clock && clock != priv->master) {
			ha_set_clock_source(priv, clock);
		}
	}

	curlen = snprintf(response, resplen, "Success");

	return curlen;
}

static int ha_handle_valid_sources_msg(struct phc2sys_private *priv,
			struct config *cfg, char *response, size_t resplen)
{
	size_t curlen = 0;
	struct clock *clock = NULL;

	LIST_FOREACH(clock, &priv->clocks, list) {
		if (clock_match_ha_requirements(clock, cfg)) {
			curlen += snprintf(response + curlen, resplen - curlen,
				"%s ", clock->device);
		}
	}

	/* no clock is matching requirements */
	if (0 == curlen) {
		curlen = snprintf(response, resplen, "None");
	}

	return curlen;
}

static int ha_com_socket_handle_msg(struct phc2sys_private *priv,
			struct config *cfg)
{
	int cnt, res = 0, fd;
	void * buffer = NULL;
	void * response = NULL;

	while(1) {
		fd = accept(priv->ha_socket_fd, NULL, NULL);
		if (fd < 0) {
			if (errno == EAGAIN || errno == EWOULDBLOCK) {
				/* no msg available */
			} else {
				pr_err("ha_com_socket: accept failed: %m");
				res = -1;
			}
			break;
		}

		buffer = malloc(HA_SCK_BUFFER_SIZE);
		if (!buffer) {
			pr_err("ha_com_socket: failed to allocate memory for message");
			close(fd);
			res = -1;
			break;
		}

		res = ha_com_socket_recv(fd, buffer, HA_SCK_BUFFER_SIZE);
		if (res < 0) {
			close(fd);
			break;
		}

		pr_debug("ha_com_socket: command received: %s", (char*)buffer);

		response = malloc(HA_SCK_BUFFER_SIZE);
		if (!response) {
			pr_err("ha_com_socket: failed to allocate memory for response message");
			close(fd);
			res = -1;
			break;
		}

		/* handle messages and create responses */
		if (strcmp((const char*)buffer, "status") == 0) {
			cnt = ha_handle_status_msg(priv, response, HA_SCK_BUFFER_SIZE);
		} else if (strcmp((const char*)buffer, "clock source") == 0) {
			if (priv->master) {
				cnt = snprintf((char*)response, HA_SCK_BUFFER_SIZE, "%s",
					priv->master->device);
			} else {
				cnt = snprintf((char*)buffer, HA_SCK_BUFFER_SIZE, "None");
			}
		} else if (strcmp((const char*)buffer, "forced lock") == 0) {
			cnt = snprintf((char*)response, HA_SCK_BUFFER_SIZE, "%s",
				priv->forced_source_clock ? "True" : "False");
		} else if (starts_with("enable lock", buffer)) {
			cnt = ha_handle_enable_lock_msg(priv, buffer, response,
					HA_SCK_BUFFER_SIZE);
		} else if (strcmp((const char*)buffer, "disable lock") == 0) {
			cnt = ha_handle_disable_lock_msg(priv, cfg, response,
					HA_SCK_BUFFER_SIZE);
		} else if (starts_with("enable source", buffer)) {
			cnt = ha_handle_enable_source_msg(priv, cfg, buffer, response,
					HA_SCK_BUFFER_SIZE);
		} else if (starts_with("disable source", buffer)) {
			cnt = ha_handle_disable_source_msg(priv, cfg, buffer, response,
					HA_SCK_BUFFER_SIZE);
		} else if (strcmp((const char*)buffer, "valid sources") == 0) {
			cnt = ha_handle_valid_sources_msg(priv, cfg, response,
					HA_SCK_BUFFER_SIZE);
		} else {
			cnt = snprintf((char*)response, HA_SCK_BUFFER_SIZE,
					"Error: Invalid command");
		}

		pr_debug("ha_com_socket: response: %s", (char*)response);

		res = ha_com_socket_send(fd, response, cnt);

		close(fd);
	}

	free(buffer);
	free(response);
	return res;
}

static int do_loop(struct phc2sys_private *priv, struct config *cfg, int subscriptions)
{
	struct timespec interval;
	struct clock *clock;
	uint64_t ts;
	int64_t offset, delay;
	int err;
	struct pmc_agent *node = NULL;
	int ha_enabled = config_get_int(cfg, NULL, "ha_enabled");
	struct timespec now;

	interval.tv_sec = priv->phc_interval;
	interval.tv_nsec = (priv->phc_interval - interval.tv_sec) * 1e9;

	while (is_running()) {
		clock_nanosleep(CLOCK_MONOTONIC, 0, &interval, NULL);

		LIST_FOREACH(node, &priv->pmc_agents, list) {
			if (pmc_agent_update(node) < 0) {
				continue;
			}

			if (ha_enabled && (node->new_dds || node->new_tpds || node->new_pds)) {
				pr_debug("pmc agent index %d clock state changed by %s%s%s",
					node->index, node->new_dds ? "new dds " : "",
					node->new_tpds ? "new tpds " : "",
					node->new_pds ? "new pds " : "");
				priv->clock_state_changed = 1;
			}

			if (subscriptions) {
				run_pmc_events(node);
				if (priv->state_changed) {
					/* force getting offset, as it may have
					 * changed after the port state change */
					if (pmc_agent_query_utc_offset(node, 1000)) {
						pr_err("failed to get UTC offset");
						continue;
					}
				}
			}
		}

		if (subscriptions && priv->state_changed) {
			reconfigure(priv);
		}

		if (ha_enabled) {
			ha_com_socket_handle_msg(priv, cfg);

			if (priv->forced_source_clock) {
				/* HA automatic clock selection is disabled */
				if (priv->clock_state_changed) {
					priv->clock_state_changed = 0;
					reset_new_dataset_flags(priv);
				}
			} else {
				if (priv->clock_state_changed) {
					clock = check_and_select_clock(priv, cfg);
					if (clock && clock != priv->master) {
						ha_set_clock_source(priv, clock);
					}

					priv->clock_state_changed = 0;
					reset_new_dataset_flags(priv);
				}

				if (priv->better) {
					/* has stability timer expired? */
					clock_gettime(CLOCK_REALTIME, &now);
					if ((now.tv_sec > priv->stability_timer.tv_sec) ||
						(now.tv_sec == priv->stability_timer.tv_sec &&
						now.tv_nsec > priv->stability_timer.tv_nsec)) {
						ha_set_clock_source(priv, priv->better);
					}
				}
			}
		}

		if (!priv->master)
			continue;

		LIST_FOREACH(clock, &priv->dst_clocks, dst_list) {
			if (!update_needed(clock))
				continue;

			/* don't try to synchronize the clock to itself */
			if (clock->clkid == priv->master->clkid ||
			    (clock->phc_index >= 0 &&
			     clock->phc_index == priv->master->phc_index) ||
			    !strcmp(clock->device, priv->master->device))
				continue;

			if (!clock->servo) {
				pr_err("cannot update clock without servo");
				return -1;
			}

			if (clock->clkid == CLOCK_REALTIME &&
			    priv->master->sysoff_method >= 0) {
				/* use sysoff */
				err = sysoff_measure(CLOCKID_TO_FD(priv->master->clkid),
						     priv->master->sysoff_method,
						     priv->phc_readings,
						     &offset, &ts, &delay);
			} else if (priv->master->clkid == CLOCK_REALTIME &&
				   clock->sysoff_method >= 0) {
				/* use reversed sysoff */
				err = sysoff_measure(CLOCKID_TO_FD(clock->clkid),
						     clock->sysoff_method,
						     priv->phc_readings,
						     &offset, &ts, &delay);
				if (!err) {
					offset = -offset;
					ts += offset;
				}
			} else {
				err = 0;
				/* use phc */
				if (!read_phc(priv->master->clkid, clock->clkid,
					      priv->phc_readings,
					      &offset, &ts, &delay))
					continue;
			}
			if (err == -EBUSY)
				continue;
			if (err)
				return -1;

			update_clock(priv, clock, offset, ts, delay);
		}
	}

	return 0;
}

static int normalize_state(int state)
{
	if (state != PS_MASTER && state != PS_SLAVE &&
	    state != PS_PRE_MASTER && state != PS_UNCALIBRATED) {
		/* treat any other state as "not a master nor a slave" */
		state = PS_DISABLED;
	}
	return state;
}

static int clock_compute_state(struct phc2sys_private *priv,
			       struct clock *clock)
{
	struct port *p;
	int state = PS_DISABLED;

	LIST_FOREACH(p, &priv->ports, list) {
		if (p->clock != clock)
			continue;
		/* PS_SLAVE takes the highest precedence, PS_UNCALIBRATED
		 * after that, PS_MASTER is third, PS_PRE_MASTER fourth and
		 * all of that overrides PS_DISABLED, which corresponds
		 * nicely with the numerical values */
		if (p->state > state)
			state = p->state;
	}
	return state;
}

static int phc2sys_recv_subscribed(struct pmc_agent *node, void *context, struct ptp_message *msg,
				   int excluded)
{
	struct phc2sys_private *priv = (struct phc2sys_private *) context;
	int mgt_id, state;
	struct portDS *pds;
	struct port *port;
	struct clock *clock;
	unsigned int port_id;

	mgt_id = management_tlv_id(msg);
	if (mgt_id == excluded)
		return 0;
	switch (mgt_id) {
	case MID_PORT_DATA_SET:
		pds = (struct portDS *)management_tlv_data(msg);
		port_id = PORT_INDEX_TO_PORT_ID(pds->portIdentity.portNumber, node->index);
		port = port_get(priv, port_id);
		if (!port) {
			pr_info("received data for unknown port %s",
				pid2str(&pds->portIdentity));
			return 1;
		}
		state = normalize_state(pds->portState);
		if (port->state != state) {
			pr_info("port %s changed state",
				pid2str(&pds->portIdentity));
			port->state = state;
			clock = port->clock;
			state = clock_compute_state(priv, clock);
			if (clock->state != state || clock->new_state) {
				clock->new_state = state;
				priv->state_changed = 1;
			}
		}
		return 1;
	}
	return 0;
}

static int auto_init_ports(struct phc2sys_private *priv, int add_rt)
{
	int err, number_ports, state, timestamping;
	char iface[IFNAMSIZ];
	struct clock *clock;
	struct port *port;
	unsigned int i;
	struct pmc_agent *node = NULL;
	unsigned int retries, port_id;

	LIST_FOREACH(node, &priv->pmc_agents, list) {
		retries = 0;
		while(retries < 10) {
			if (!is_running()) {
				return -1;
			}
			err = pmc_agent_query_dds(node, 1000);
			if (!err) {
				break;
			}
			if (err == -ETIMEDOUT) {
				pr_notice("Waiting for ptp4l...");
				retries++;
			} else {
				return -1;
			}
		}

		number_ports = pmc_agent_get_number_ports(node);
		if (number_ports <= 0) {
			pr_err("failed to get number of ports");
			continue;
		}

		err = pmc_agent_subscribe(node, 1000);
		if (err) {
			pr_err("failed to subscribe");
			continue;
		}

		for (i = 1; i <= number_ports; i++) {
			err = pmc_agent_query_port_properties(node, 1000, i,
								&state, &timestamping,
								iface);
			if (err == -ENODEV) {
				/* port does not exist, ignore the port */
				continue;
			}
			if (err) {
				pr_err("failed to get port properties");
				break;
			}
			if (timestamping == TS_SOFTWARE) {
				/* ignore ports with software time stamping */
				continue;
			}
			port_id = PORT_INDEX_TO_PORT_ID(i, node->index);
			port = port_add(priv, port_id, iface);
			if (!port)
				return -1;
			port->state = normalize_state(state);
			/* map clock to pmc agent node */
			port->clock->node = node;
		}
	}

	if (LIST_EMPTY(&priv->clocks)) {
		pr_err("no suitable ports available");
		return -1;
	}
	LIST_FOREACH(clock, &priv->clocks, list) {
		clock->new_state = clock_compute_state(priv, clock);
	}
	priv->state_changed = 1;

	if (add_rt) {
		clock = clock_add(priv, "CLOCK_REALTIME");
		if (!clock)
			return -1;
		if (add_rt == 1)
			clock->dest_only = 1;
	}

	/* get initial offset */
	LIST_FOREACH(node, &priv->pmc_agents, list) {
		if (pmc_agent_query_utc_offset(node, 1000)) {
			pr_err("failed to get UTC offset");
			continue;
		}
	}
	return 0;
}

/* Returns: non-zero to skip clock update */
static int clock_handle_leap(struct phc2sys_private *priv, struct clock *clock,
			     int64_t offset, uint64_t ts)
{
	int clock_leap, node_leap;
	struct pmc_agent *node = priv->master->node;

	node_leap = pmc_agent_get_leap(node);

	clock->sync_offset = pmc_agent_get_sync_offset(node);

	if ((node_leap || clock->leap_set) &&
	    clock->is_utc != priv->master->is_utc) {
		/* If the master clock is in UTC, get a time stamp from it, as
		   it is the clock which will include the leap second. */
		if (priv->master->is_utc) {
			struct timespec tp;
			if (clock_gettime(priv->master->clkid, &tp)) {
				pr_err("failed to read clock: %m");
				return -1;
			}
			ts = tp.tv_sec * NS_PER_SEC + tp.tv_nsec;
		}

		/* If the clock will be stepped, the time stamp has to be the
		   new time. Ignore possible 1 second error in UTC offset. */
		if (clock->is_utc && clock->servo_state == SERVO_UNLOCKED)
			ts -= offset + get_sync_offset(priv, clock);

		/* Suspend clock updates in the last second before midnight. */
		if (is_utc_ambiguous(ts)) {
			pr_info("clock update suspended due to leap second");
			return 1;
		}

		clock_leap = leap_second_status(ts, clock->leap_set,
						&node_leap,
						&clock->sync_offset);

		if (clock->leap_set != clock_leap) {
			/* Only the system clock can leap. */
			if (clock->clkid == CLOCK_REALTIME &&
			    priv->kernel_leap)
				sysclk_set_leap(clock_leap);
			else
				servo_leap(clock->servo, clock_leap);
			clock->leap_set = clock_leap;
		}
	}

	if (pmc_agent_utc_offset_traceable(node) &&
	    clock->utc_offset_set != clock->sync_offset) {
		if (clock->clkid == CLOCK_REALTIME)
			sysclk_set_tai_offset(clock->sync_offset);
		clock->utc_offset_set = clock->sync_offset;
	}

	return 0;
}

static void usage(char *progname)
{
	fprintf(stderr,
		"\n"
		"usage: %s [options]\n\n"
		"\n"
		" automatic configuration:\n"
		" -a             turn on autoconfiguration\n"
		" -r             synchronize system (realtime) clock\n"
		"                repeat -r to consider it also as a time source\n"
		" manual configuration:\n"
		" -c [dev|name]  slave clock (CLOCK_REALTIME)\n"
		" -d [dev]       master PPS device\n"
		" -s [dev|name]  master clock\n"
		" -O [offset]    slave-master time offset (0)\n"
		" -w             wait for ptp4l\n"
		" common options:\n"
		" -f [file]      configuration file\n"
		" -E [pi|linreg] clock servo (pi)\n"
		" -P [kp]        proportional constant (0.7)\n"
		" -I [ki]        integration constant (0.3)\n"
		" -S [step]      step threshold (disabled)\n"
		" -F [step]      step threshold only on start (0.00002)\n"
		" -R [rate]      slave clock update rate in HZ (1.0)\n"
		" -N [num]       number of master clock readings per update (5)\n"
		" -L [limit]     sanity frequency limit in ppb (200000000)\n"
		" -M [num]       NTP SHM segment number (0)\n"
		" -D [num]       fall back to default clock in automatic mode (1)\n"
		" -u [num]       number of clock updates in summary stats (0)\n"
		" -n [num]       domain number (0)\n"
		" -x             apply leap seconds by servo instead of kernel\n"
		" -z [path]      server address for UDS (/var/run/ptp4l)\n"
		" -l [num]       set the logging level to 'num' (6)\n"
		" -t [tag]       add tag to log messages\n"
		" -m             print messages to stdout\n"
		" -q             do not print messages to the syslog\n"
		" -v             prints the software version and exits\n"
		" -h             prints this message and exits\n"
		"\n",
		progname);
}

int main(int argc, char *argv[])
{
	char *config = NULL, *dst_name = NULL, *progname;
	char *src_names[MAX_SRC_CLOCKS];
	char uds_local[MAX_IFNAME_SIZE + 1];
	int autocfg = 0, c, domain_number = 0, index, ntpshm_segment, offset;
	int pps_fd = -1, print_level = LOG_INFO, r = -1, rt = 0;
	int wait_sync = 0;
	struct clock *src, *dst;
	struct config *cfg;
	struct option *opts;
	int default_sync = 1;
	double phc_rate, tmp;
	struct phc2sys_private priv = {
		.phc_readings = 5,
		.phc_interval = 1.0,
		.master = NULL,
		.better = NULL,
		.stability_timer.tv_sec = 0,
		.forced_source_clock = 0,
		.ha_socket_fd = -1,
	};
	struct pmc_agent *node = NULL;
	unsigned int i, src_cnt = 0;
	int ha_enabled = 0;

	handle_term_signals();

	cfg = phc2sys_config = config_create();
	if (!cfg) {
		return -1;
	}
	node = pmc_agent_add(&priv, 0);
	if (!node) {
		return -1;
	}

	opts = config_long_options(cfg);

	config_set_double(cfg, "pi_proportional_const", KP);
	config_set_double(cfg, "pi_integral_const", KI);

	/* Process the command line arguments. */
	progname = strrchr(argv[0], '/');
	progname = progname ? 1+progname : argv[0];
	while (EOF != (c = getopt_long(argc, argv,
				"arc:d:f:s:E:P:I:S:F:R:N:O:L:M:D:i:u:wn:xz:l:t:mqvh",
				opts, &index))) {
		switch (c) {
		case 0:
			if (config_parse_option(cfg, opts[index].name, optarg)) {
				goto bad_usage;
			}
			break;
		case 'a':
			autocfg = 1;
			break;
		case 'r':
			rt++;
			break;
		case 'c':
			dst_name = strdup(optarg);
			break;
		case 'd':
			pps_fd = open(optarg, O_RDONLY);
			if (pps_fd < 0) {
				fprintf(stderr,
					"cannot open '%s': %m\n", optarg);
				goto end;
			}
			break;
		case 'f':
			config = optarg;
			break;
		case 'i':
			fprintf(stderr,
				"'-i' has been deprecated. please use '-s' instead.\n");
            /* fallthrough */
		case 's':
			if (src_cnt == MAX_SRC_CLOCKS) {
				fprintf(stderr, "too many source clocks\n");
				goto bad_usage;
			}
			src_names[src_cnt++] = optarg;
			break;
		case 'E':
			if (!strcasecmp(optarg, "pi")) {
				config_set_int(cfg, "clock_servo",
					       CLOCK_SERVO_PI);
			} else if (!strcasecmp(optarg, "linreg")) {
				config_set_int(cfg, "clock_servo",
					       CLOCK_SERVO_LINREG);
			} else if (!strcasecmp(optarg, "ntpshm")) {
				config_set_int(cfg, "clock_servo",
					       CLOCK_SERVO_NTPSHM);
			} else {
				fprintf(stderr,
					"invalid servo name %s\n", optarg);
				goto end;
			}
			break;
		case 'P':
			if (get_arg_val_d(c, optarg, &tmp, 0.0, DBL_MAX) ||
			    config_set_double(cfg, "pi_proportional_const", tmp))
				goto end;
			break;
		case 'I':
			if (get_arg_val_d(c, optarg, &tmp, 0.0, DBL_MAX) ||
			    config_set_double(cfg, "pi_integral_const", tmp))
				goto end;
			break;
		case 'S':
			if (get_arg_val_d(c, optarg, &tmp, 0.0, DBL_MAX) ||
			    config_set_double(cfg, "step_threshold", tmp))
				goto end;
			break;
		case 'F':
			if (get_arg_val_d(c, optarg, &tmp, 0.0, DBL_MAX) ||
			    config_set_double(cfg, "first_step_threshold", tmp))
				goto end;
			break;
		case 'R':
			if (get_arg_val_d(c, optarg, &phc_rate, 1e-9, DBL_MAX))
				goto end;
			priv.phc_interval = 1.0 / phc_rate;
			break;
		case 'N':
			if (get_arg_val_i(c, optarg, &priv.phc_readings, 1, INT_MAX))
				goto end;
			break;
		case 'O':
			if (get_arg_val_i(c, optarg, &offset, INT_MIN, INT_MAX)) {
				goto end;
			}
			pmc_agent_set_sync_offset(node, offset);
			priv.forced_sync_offset = -1;
			break;
		case 'L':
			if (get_arg_val_i(c, optarg, &priv.sanity_freq_limit, 0, INT_MAX) ||
			    config_set_int(cfg, "sanity_freq_limit", priv.sanity_freq_limit)) {
				goto end;
			}
			break;
		case 'M':
			if (get_arg_val_i(c, optarg, &ntpshm_segment, INT_MIN, INT_MAX) ||
			    config_set_int(cfg, "ntpshm_segment", ntpshm_segment))
				goto end;
			break;
		case 'u':
			if (get_arg_val_ui(c, optarg, &priv.stats_max_count,
					  0, UINT_MAX))
				goto end;
			break;
		case 'w':
			wait_sync = 1;
			break;
		case 'n':
			if (get_arg_val_i(c, optarg, &domain_number, 0, 255) ||
			    config_set_int(cfg, "domainNumber", domain_number)) {
				goto end;
			}
			break;
		case 'x':
			if (config_set_int(cfg, "kernel_leap", 0)) {
				goto end;
			}
			break;
		case 'z':
			if (strlen(optarg) > MAX_IFNAME_SIZE) {
				fprintf(stderr, "path %s too long, max is %d\n",
					optarg, MAX_IFNAME_SIZE);
				goto end;
			}
			if (config_set_string(cfg, "uds_address", optarg)) {
				goto end;
			}
			break;
		case 'l':
			if (get_arg_val_i(c, optarg, &print_level,
					  PRINT_LEVEL_MIN, PRINT_LEVEL_MAX) ||
			    config_set_int(cfg, "logging_level", print_level)) {
				goto end;
			}
			break;
		case 't':
			if (config_set_string(cfg, "message_tag", optarg)) {
				goto end;
			}
			break;
		case 'm':
			if (config_set_int(cfg, "verbose", 1)) {
				goto end;
			}
			break;
		case 'q':
			if (config_set_int(cfg, "use_syslog", 0)) {
				goto end;
			}
			break;
		case 'v':
			version_show(stdout);
			config_destroy(cfg);
			return 0;
		case 'D':
			if (get_arg_val_i(c, optarg, &default_sync, 0, 1) ||
			config_set_int(cfg, "default_sync", default_sync)) {
				goto end;
			}
			break;
		case 'h':
			usage(progname);
			config_destroy(cfg);
			return 0;
		default:
			goto bad_usage;
		}
	}

	if (config && (c = config_read(config, cfg))) {
		return c;
	}

	ha_enabled = config_get_int(cfg, NULL, "ha_enabled");
	if (ha_enabled && src_cnt == 0) {
		/* get the source interface list from configuration file */
		src_cnt = config_get_interfaces(cfg, src_names, MAX_SRC_CLOCKS);
		if (src_cnt == (unsigned int)-1) {
			fprintf(stderr, "too many interfaces in configuration file\n");
			fprintf(stderr, "maximum number of interfaces is %u\n", MAX_SRC_CLOCKS);
			goto bad_usage;
		}
	}

	if (autocfg && (src_cnt > 0 || dst_name || pps_fd >= 0 || wait_sync || priv.forced_sync_offset)) {
		fprintf(stderr,
			"autoconfiguration cannot be mixed with manual config options.\n");
		goto bad_usage;
	}
	if (!autocfg && pps_fd < 0 && src_cnt == 0) {
		fprintf(stderr,
			"autoconfiguration or valid source clock must be selected.\n");
		goto bad_usage;
	}

	if (!autocfg && !wait_sync && !priv.forced_sync_offset) {
		fprintf(stderr,
			"time offset must be specified using -w or -O\n");
		goto bad_usage;
	}

	if (priv.servo_type == CLOCK_SERVO_NTPSHM) {
		priv.kernel_leap = 0;
		priv.sanity_freq_limit = 0;
	}

	print_set_progname(progname);
	print_set_tag(config_get_string(cfg, NULL, "message_tag"));
	print_set_verbose(config_get_int(cfg, NULL, "verbose"));
	print_set_syslog(config_get_int(cfg, NULL, "use_syslog"));
	print_set_level(config_get_int(cfg, NULL, "logging_level"));

	priv.servo_type = config_get_int(cfg, NULL, "clock_servo");
	if (priv.servo_type == CLOCK_SERVO_NTPSHM) {
		config_set_int(cfg, "kernel_leap", 0);
		config_set_int(cfg, "sanity_freq_limit", 0);
	}
	priv.kernel_leap = config_get_int(cfg, NULL, "kernel_leap");
	priv.sanity_freq_limit = config_get_int(cfg, NULL, "sanity_freq_limit");
	priv.default_sync = config_get_int(cfg, NULL, "default_sync");

	snprintf(uds_local, sizeof(uds_local), "/var/run/phc2sys.%d",
		 getpid());

	if (autocfg) {
		domain_number = config_get_int(cfg, NULL, "domainNumber");
		if (init_pmc_node(cfg, node, uds_local, domain_number,
				  phc2sys_recv_subscribed, &priv))
			goto end;
		if (auto_init_ports(&priv, rt) < 0)
			goto end;
		r = do_loop(&priv, cfg, 1);
		goto end;
	}

	if (!ha_enabled && src_cnt > 1) {
		fprintf(stderr, "too many source clocks\n");
		fprintf(stderr, "Use 'ha_enabled 1' to accept more than one source clock\n");
		goto bad_usage;
	}

	for (i = 0; i < src_cnt; ++i) {
		src = clock_add(&priv, src_names[i]);
		if (!src) {
			fprintf(stderr,
				"invalid source clock '%s'.\n", src_names[i]);
			goto bad_usage;
		}
		src->state = PS_SLAVE;
		/* select the first clock */
		if (priv.master == NULL) {
			priv.master = src;
		}
		if (i > 0) {
			node = pmc_agent_add(&priv, i);
			if (!node)
				goto end;
		}
		/* map clock to pmc agent node */
		src->node = node;
		pr_debug("pmc node index %d assigned to source interface %s",
			node->index, src->device);
		if (ha_enabled) {
			src->ha_priority = config_get_int(cfg, src->device, "ha_priority");
		}
	}

	dst = clock_add(&priv, dst_name ? dst_name : "CLOCK_REALTIME");
	free(dst_name);
	if (!dst) {
		fprintf(stderr,
			"valid destination clock must be selected.\n");
		goto bad_usage;
	}
	dst->state = PS_MASTER;
	LIST_INSERT_HEAD(&priv.dst_clocks, dst, dst_list);

	if (pps_fd >= 0 && dst->clkid != CLOCK_REALTIME) {
		fprintf(stderr,
			"cannot use a pps device unless destination is CLOCK_REALTIME\n");
		goto bad_usage;
	}

	if (ha_enabled) {
		src = ha_forced_source_clock(&priv, cfg);
		if (src != NULL) {
			pr_info("Only interface %s will be used as source clock", src->device);
			priv.master = src;
		}
	}

	r = -1;

	if (wait_sync) {
		LIST_FOREACH(src, &priv.clocks, list) {

			/* skip dst clock */
			if (src->state == PS_MASTER)
				continue;

			/* uds local is formated '/var/run/phc2sys.<pid>.<source_interface>' */
			snprintf(uds_local, sizeof(uds_local), "/var/run/phc2sys.%d.%s",
				getpid(), src->device);

			if (config_is_option_set(cfg, src->device, "ha_domainNumber")) {
				domain_number = config_get_int(cfg, src->device,
					"ha_domainNumber");
			} else {
				domain_number = config_get_int(cfg, NULL, "domainNumber");
			}
			if (init_pmc_node(cfg, src->node, uds_local, domain_number,
					phc2sys_recv_subscribed, &priv))
				goto end;

			while (is_running()) {
				r = run_pmc_wait_sync(src->node, 1000);
				if (r < 0)
					goto end;
				if (r > 0)
					break;
				else
					pr_notice("Waiting for ptp4l...");
			}

			if (!priv.forced_sync_offset) {
				r = pmc_agent_query_utc_offset(src->node, 1000);
				if (r) {
					pr_err("failed to get UTC offset");
					goto end;
				}
			}

			if (priv.forced_sync_offset ||
				(src->clkid != CLOCK_REALTIME && dst->clkid != CLOCK_REALTIME) ||
				src->clkid == CLOCK_INVALID) {
				pmc_agent_disable(src->node);
			}
		}

		if (ha_enabled && !priv.forced_source_clock) {
			priv.master = ha_select_clock(&priv, cfg);
			pr_info("interface %s will be used as source clock", priv.master->device);
		}
	}

	if (ha_enabled) {
		ha_com_socket_open(&priv.ha_socket_fd, cfg);
	}

	if (pps_fd >= 0) {
		/* only one destination clock allowed with PPS until we
		 * implement a mean to specify PTP port to PPS mapping */
		servo_sync_interval(dst->servo, 1.0);
		r = do_pps_loop(&priv, dst, pps_fd);
	} else {
		r = do_loop(&priv, cfg, 0);
	}

end:
	ha_com_socket_close(priv.ha_socket_fd);
	pmc_agent_cleanup(&priv);
	clock_cleanup(&priv);
	port_cleanup(&priv);
	config_destroy(cfg);
	msg_cleanup();
	return r;
bad_usage:
	usage(progname);
	config_destroy(cfg);
	return -1;
}
