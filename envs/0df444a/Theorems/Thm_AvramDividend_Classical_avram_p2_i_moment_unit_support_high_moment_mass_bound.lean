-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_i_moment_unit_support_high_moment_mass_bound
-- name    : AvramDividend.Classical.avram_p2_i_moment_unit_support_high_moment_mass_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T17:18:30.60586+00:00
-- url     : https://prove2.me/theorems/47f9dd4c-58df-4baf-8018-ac056a04360e
-- title:
--   Every high nonnegative moment of a unit-supported positive measure is bounded by its mass
-- statement:
--   For any positive measure supported almost everywhere on the real interval [0,1], every nonnegative integer moment expressed as an ENNReal lintegral is bounded by the measure's total mass. The measure need not be a probability measure. This supplies the uniform-in-degree limiting moment cap used to suppress polynomial approximation tails from approximating measures that may place mass above 1.

import Mathlib
open MeasureTheory Set
open scoped ENNReal

theorem AvramDividend.Classical.avram_p2_i_moment_unit_support_high_moment_mass_bound
    (μ : Measure ℝ)
    (hμ : ∀ᵐ z ∂μ, z ∈ Set.Icc (0 : ℝ) 1)
    (k : ℕ) :
    (∫⁻ z : ℝ, (ENNReal.ofReal z) ^ k ∂μ) ≤ μ Set.univ := by sorry
