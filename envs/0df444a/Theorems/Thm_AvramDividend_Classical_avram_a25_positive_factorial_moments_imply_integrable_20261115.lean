-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a25_positive_factorial_moments_imply_integrable_20261115
-- name    : AvramDividend.Classical.avram_a25_positive_factorial_moments_imply_integrable_20261115
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T07:32:25.746223+00:00
-- url     : https://prove2.me/theorems/e123c35b-7c1b-482a-b73c-f01324542f59
-- title:
--   Strictly positive factorial moments certify actual Bochner integrability
-- statement:
--   If a natural count has every descending factorial Bochner integral equal to r^n and r>0, all factorial moment functions are Bochner integrable. The integral is nonzero for every n, and Mathlib's Integrable.of_integral_ne_zero establishes integrability because a nonintegrable function would have Bochner integral zero. This addresses a potentially dangerous zero-rate loophole in formal moment-characterisation arguments.
-- source:
--   MeasureTheory.Integrable.of_integral_ne_zero and positivity of r^n for r>0, pinned Mathlib.

import Mathlib
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Nat
noncomputable section

theorem AvramDividend.Classical.avram_a25_positive_factorial_moments_imply_integrable_20261115
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (K : Ω → ℕ) (r : ℝ≥0) (hr : 0 < r)
    (hMom : ∀ n : ℕ,
      (∫ ω, (Nat.descFactorial (K ω) n : ℝ) ∂P) = (r : ℝ) ^ n) :
    ∀ n : ℕ,
      Integrable (fun ω => (Nat.descFactorial (K ω) n : ℝ)) P := by sorry
