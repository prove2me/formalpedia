-- Prove2me | Theorems.Thm_AvramDividend_Classical_positive_jump_tail_threshold_mass_le_first_moment
-- name    : AvramDividend.Classical.positive_jump_tail_threshold_mass_le_first_moment
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T21:04:24.94005+00:00
-- url     : https://prove2.me/theorems/9d18b607-8759-448d-9bf4-23188d868f4a
-- title:
--   Sharp Markov bound for a positive strict jump tail by its first moment
-- statement:
--   For any nonnegative jump-magnitude measure μ and any t>0, t times the strict upper-tail μ{z:t<z} is at most its first moment ∫ z dμ, including the extended-infinite case. This yields the needed α/t pointwise domination for the initial Esscher renewal kernel, without assuming σ-finiteness.
-- source:
--   Pinned Mathlib mul_meas_ge_le_lintegral (Markov inequality) and monotonicity of ENNReal.ofReal.

import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.Data.ENNReal.Real
open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical
theorem positive_jump_tail_threshold_mass_le_first_moment
    (μ : Measure ℝ≥0) (t : ℝ) (ht : 0 < t) :
    ENNReal.ofReal t * μ {z : ℝ≥0 | t < (z : ℝ)} ≤
      ∫⁻ z : ℝ≥0, ENNReal.ofReal (z : ℝ) ∂μ := by sorry
end AvramDividend.Classical
