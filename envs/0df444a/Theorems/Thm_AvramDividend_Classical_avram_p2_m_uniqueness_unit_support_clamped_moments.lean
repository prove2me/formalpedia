-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_m_uniqueness_unit_support_clamped_moments
-- name    : AvramDividend.Classical.avram_p2_m_uniqueness_unit_support_clamped_moments
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T16:24:31.879228+00:00
-- url     : https://prove2.me/theorems/66462848-bef6-4e25-92b1-d7c5eb9371f0
-- title:
--   Unit-supported monomial moments agree with bounded clamped tests
-- statement:
--   For a finite real measure supported on [0,1], any bounded continuous NNReal test whose ENNReal embedding equals ENNReal.ofReal on the unit interval has equal kth lintegral moments. This is the exact support-dependent bridge from original Lévy image monomials to the weak-cluster continuity theorem.

import Mathlib
open MeasureTheory Set BoundedContinuousFunction
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_m_uniqueness_unit_support_clamped_moments
    (μ : FiniteMeasure ℝ) (f : ℝ →ᵇ ℝ≥0) (k : ℕ)
    (hunit : μ (Set.Icc (0 : ℝ) 1)ᶜ = 0)
    (hagree : ∀ z : ℝ, z ∈ Set.Icc (0 : ℝ) 1 →
      (f z : ℝ≥0∞) = ENNReal.ofReal z) :
    (∫⁻ z, (f z : ℝ≥0∞) ^ k ∂μ) =
      (∫⁻ z, (ENNReal.ofReal z) ^ k ∂μ) := by sorry
