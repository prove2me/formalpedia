-- Prove2me | Theorems.Thm_AvramDividend_Classical_barrierStrategy_zero_boundary_of_positive_ratio_and_divergent_deriv
-- name    : AvramDividend.Classical.barrierStrategy_zero_boundary_of_positive_ratio_and_divergent_deriv
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T12:51:05.86099+00:00
-- url     : https://prove2.me/theorems/24c96388-6b8a-4846-9c42-706f1428b302
-- title:
--   Zero-barrier reflected value from positive scale ratios and diverging right derivative
-- statement:
--   When actual positive-barrier stopped reflected rewards satisfy the scale-quotient formula and W is continuous from the right while W'(x) tends +∞ as x decreases to zero, the zero-barrier dividend value equals the exact boundary scale expression. Both sides vanish because the extended zero-right derivative is infinite.
-- source:
--   Pinned Mathlib one-sided topology, existing accepted infinite scale-ratio limit and derivative conversion, canonical zero-barrier stochastic monotone limit transfer.

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.ContinuousOn
import Mathlib.Tactic.Positivity
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_zero_boundary_of_positive_scale_limit
import Theorems.Thm_AvramDividend_Classical_scale_ratio_reciprocal_tendsto_of_deriv_atTop
import Theorems.Thm_AvramDividend_Classical_barrierValue_zero_of_derivZeroPlus_top
import Theorems.Thm_AvramDividend_Classical_derivZeroPlus_eq_top_of_right_tendsto_atTop

open AvramDividend.Classical MeasureTheory Filter Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.barrierStrategy_zero_boundary_of_positive_ratio_and_divergent_deriv
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ) (W : ℝ → ℝ)
    (hscale : ∀ n : ℕ,
      barrierSupValue X (1 / ((n : ℝ) + 1)) q =
        ENNReal.ofReal (W (1 / ((n : ℝ) + 1)) /
          deriv W (1 / ((n : ℝ) + 1))))
    (hcont : ContinuousWithinAt W (Ici (0 : ℝ)) 0)
    (hderiv : Tendsto (fun y : ℝ => deriv W y)
      (nhdsWithin (0 : ℝ) (Ioi 0)) atTop) :
    dividendValue X q 0 (barrierStrategy X 0 0) =
      ENNReal.ofReal (barrierValue W 0 0) := by sorry
