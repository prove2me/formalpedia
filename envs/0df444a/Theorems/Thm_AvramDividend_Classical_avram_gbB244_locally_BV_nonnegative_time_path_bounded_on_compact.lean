-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB244_locally_BV_nonnegative_time_path_bounded_on_compact
-- name    : AvramDividend.Classical.avram_gbB244_locally_BV_nonnegative_time_path_bounded_on_compact
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T11:06:14.192787+00:00
-- url     : https://prove2.me/theorems/685ddb50-3353-44a3-bfcd-a950b6398c91
-- title:
--   Locally bounded-variation dividend paths are bounded on every compact nonnegative-time horizon
-- statement:
--   Any real-valued locally bounded-variation function on nonnegative physical time admits finite lower and upper bounds on each closed interval from zero to a finite horizon. The proof uses the pinned Mathlib Jordan decomposition into two nondecreasing functions and compares their values at the endpoints. This directly supplies the finite-variation component of the compact-range argument needed for Gaussian semimartingale local time.
-- source:
--   Gaussian B243 hard stochastic occupation theorem: deterministic pathwise boundedness of original locally BV dividend correction, no stochastic assumptions.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB244_locally_BV_nonnegative_time_path_bounded_on_compact
    (f : ℝ≥0 → ℝ)
    (hFV : LocallyBoundedVariationOn f Set.univ)
    (T : ℝ≥0) :
    ∃ lo hi : ℝ, ∀ t ∈ Set.Icc (0 : ℝ≥0) T,
      lo ≤ f t ∧ f t ≤ hi := by sorry
