-- Prove2me | Theorems.Thm_AvramDividend_Classical_lintegral_le_of_null_nonpositive_and_positive_truncation_bounds
-- name    : AvramDividend.Classical.lintegral_le_of_null_nonpositive_and_positive_truncation_bounds
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T20:43:46.901865+00:00
-- url     : https://prove2.me/theorems/4b7a6799-d1e8-4fb4-a3f3-9903238c6792
-- title:
--   Uniform finite positive-time integral bounds extend to the full integral when nonpositive mass vanishes
-- statement:
--   A nonnegative measurable reward on real time with a measure assigning zero mass to nonpositive times has its full Lebesgue integral bounded by B whenever the integrals on every positive bounded truncation (0,n] are bounded by B. This is the monotone-convergence bridge needed to pass the reflected dividend first-record budgets from finite horizons to the full stopped reward.
-- source:
--   Measurable positive-window indicators, monotone convergence (lintegral_iSup), real Archimedean exhaustions and the zero-measure nonpositive support hypothesis.

import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

open MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.lintegral_le_of_null_nonpositive_and_positive_truncation_bounds
    (μ : Measure ℝ)
    (hzero : μ (Set.Iic (0 : ℝ)) = 0)
    (f : ℝ → ℝ≥0∞) (hf : Measurable f) (B : ℝ≥0∞)
    (hbound : ∀ n : ℕ,
      (∫⁻ r, if r ∈ Set.Ioc (0 : ℝ) (n : ℝ) then f r else 0 ∂μ) ≤ B) :
    (∫⁻ r, f r ∂μ) ≤ B := by sorry
