-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB246_locally_BV_time_path_discontinuities_countable
-- name    : AvramDividend.Classical.avram_gbB246_locally_BV_time_path_discontinuities_countable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T11:22:55.704567+00:00
-- url     : https://prove2.me/theorems/4d9df01e-3886-4b63-8b8a-70852bd776d4
-- title:
--   Locally bounded-variation nonnegative-time paths have at most countably many discontinuities
-- statement:
--   An arbitrary locally bounded variation real-valued path on nonnegative time has at most countably many points of discontinuity, by its exact Jordan decomposition into two monotone functions. This supplies generic source-preserving time-continuity ingredients for the Gaussian martingale plus original finite-variation dividend process, prior to any stochastic local-time argument.
-- source:
--   Generic time BV discontinuity lemma for B243 stochastic occupation and B247, using Mathlib Monotone.countable_not_continuousAt and LocallyBoundedVariationOn.exists_monotoneOn_sub_monotoneOn.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB246_locally_BV_time_path_discontinuities_countable
    (f : ℝ≥0 → ℝ)
    (hf : LocallyBoundedVariationOn f Set.univ) :
    Set.Countable {t : ℝ≥0 | ¬ ContinuousAt f t} := by sorry
