-- Prove2me | Theorems.Thm_AvramDividend_Classical_positiveLaplace_geometric_measure_sum
-- name    : AvramDividend.Classical.positiveLaplace_geometric_measure_sum
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-04T00:18:22.107607+00:00
-- url     : https://prove2.me/theorems/55d8e098-8f15-40a9-b947-e1f8c263bea4
-- title:
--   Closed Laplace transform for geometric countable renewal measure sums
-- statement:
--   Given a sequence m_n of positive measures whose nonnegative Laplace transforms at θ are exactly a^n, the Laplace transform of the countable measure sum Σ_n c^(n+1)m_n is c/(1-ca), interpreted in the extended nonnegative reals. This is the exact geometric-resolvent inversion step required to construct the positive bounded-variation Lévy q-scale-function renewal measure from convolution powers, with no unproved interchange of integrals and sums.
-- source:
--   Pinned Mathlib MeasureTheory.Integral.Lebesgue.Basic lintegral_sum_measure, lintegral_smul_measure; Analysis.SpecificLimits.Basic ENNReal.tsum_geometric

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

/-- The positive Laplace transform of a geometric sum of measures can be
evaluated from the transforms of its individual terms. -/
theorem positiveLaplace_geometric_measure_sum (m : ℕ → Measure ℝ) (θ : ℝ) (a c : ℝ≥0∞)
    (hm : ∀ n : ℕ,
      (∫⁻ x : ℝ, ENNReal.ofReal (Real.exp (-θ * x)) ∂m n) = a ^ n) :
    (∫⁻ x : ℝ, ENNReal.ofReal (Real.exp (-θ * x)) ∂
       Measure.sum (fun n : ℕ => c ^ (n + 1) • m n)) =
      c * (1 - c * a)⁻¹ := by
  sorry

end AvramDividend.Classical
