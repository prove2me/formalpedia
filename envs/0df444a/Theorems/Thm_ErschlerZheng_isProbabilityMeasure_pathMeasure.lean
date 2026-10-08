-- Prove2me | Theorems.Thm_ErschlerZheng_isProbabilityMeasure_pathMeasure
-- name    : ErschlerZheng.isProbabilityMeasure_pathMeasure
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-06T11:14:32.584543+00:00
-- url     : https://prove2.me/theorems/8a631d33-a228-42e6-976b-19c82408b9a3
-- title:
--   p. 9, bundle reading — for a probability μ on a group whose points are measurable, the law ℙ_x of the trajectory of the μ-random walk is a probability measure
-- statement:
--   Let $G$ be a group with a $\sigma$-algebra in which every singleton is measurable (`MeasurableSingletonClass G`; the discrete $\sigma$-algebra is one, by Mathlib's instance `DiscreteMeasurableSpace.toMeasurableSingletonClass`), and let $\mu$ be a probability on $G$ (`IsProbability`). Then for every $x \in G$ the law $\mathbb P_x$ of the trajectory $(W_0, W_1, \ldots)$ of the $\mu$-random walk started at $x$ (`pathMeasure μ x`) is a probability measure on $G^{\mathbb N}$ (`MeasureTheory.IsProbabilityMeasure`). The statement does not assume that $G$ is countable.
--
--   This is not a result of the paper. It backs the sentence of the Walks bundle note `ErschlerZheng_Walks` saying that the Mathlib constructions behind `pathMeasure` do not return the zero measure for a probability $\mu$ on a countable group with the discrete $\sigma$-algebra, the setting of the Kaimanovich–Vershik milestone `KaimanovichVershik.hasNontrivialPoissonBoundary_iff_exists_isShiftInvariant_pathMeasure_pos_lt_one`, which is stated through `pathMeasure`.
-- source:
--   Erschler, A. and Zheng, T., Growth of periodic Grigorchuk groups, Invent. Math. 219 (2020) 1069–1155, https://doi.org/10.1007/s00222-019-00922-0 (arXiv:1802.09077v2, whose page numbers are used), p. 9, the law of the trajectory is a probability (supporting fact, not in the paper)

import Mathlib
import Definitions.Def_ErschlerZheng_Walks

namespace ErschlerZheng

theorem isProbabilityMeasure_pathMeasure {G : Type*} [Group G] [MeasurableSpace G]
    [MeasurableSingletonClass G] (μ : G → ℝ) (hμ : IsProbability μ) (x : G) :
    MeasureTheory.IsProbabilityMeasure (pathMeasure μ x) := by
  sorry

end ErschlerZheng
