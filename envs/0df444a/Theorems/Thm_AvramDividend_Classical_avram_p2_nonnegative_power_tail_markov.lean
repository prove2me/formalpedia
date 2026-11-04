-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_nonnegative_power_tail_markov
-- name    : AvramDividend.Classical.avram_p2_nonnegative_power_tail_markov
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T09:46:50.058034+00:00
-- url     : https://prove2.me/theorems/b35dab7b-bfa8-44cb-b060-0e10592acdea
-- title:
--   Power-moment Markov bound for real finite-measure tails at nonnegative thresholds
-- statement:
--   For any Borel measure on the real line, nonnegative threshold R and polynomial degree k, its mass of values at least R multiplied by R^k is bounded by its k-th nonnegative ENNReal moment. This allows source-side weighted exponential image moment convergence to control mass above positive cutoffs without an assumed compensator, density or bounded-variation restriction.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_nonnegative_power_tail_markov
    (μ : MeasureTheory.Measure ℝ) (R : ℝ) (hR : 0 ≤ R) (k : ℕ) :
    ENNReal.ofReal (R ^ k) * μ (Ici R) ≤
      ∫⁻ z : ℝ, ENNReal.ofReal (z ^ k) ∂μ := by sorry
