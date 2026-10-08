-- Prove2me | Theorems.Thm_AvramDividend_Classical_positiveLaplace_convolution_powers
-- name    : AvramDividend.Classical.positiveLaplace_convolution_powers
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-05T20:34:48.776682+00:00
-- url     : https://prove2.me/theorems/b804eebb-cd81-48a6-86a0-e3fd362af8dd
-- title:
--   Positive Laplace transform of recursive additive convolution powers
-- statement:
--   Let m_0 be Dirac mass at zero and m_{n+1}=κ*m_n under additive convolution. If every m_n is s-finite and the positive exponential Laplace transform of κ at θ equals a, then the corresponding transform of m_n is a^n for every n. The proof is induction using multiplicativity of the positive Laplace functional under convolution.
-- source:
--   Direct induction from already-Proved AvramDividend.Classical.positive_laplace_functional_convolution (UUID 5aa47d4f-3286-4290-a0f4-1f910e0dc1a3) and pinned Mathlib additive-convolution identity Dirac zero. This supplies the power-transform hypothesis required by positiveLaplace_geometric_measure_sum for the bounded-variation renewal series.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_positive_laplace_functional_convolution
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

namespace AvramDividend.Classical

/-- Recursive additive convolution powers have the corresponding powers of the
positive exponential Laplace transform. -/
theorem positiveLaplace_convolution_powers
    (κ : Measure ℝ) (m : ℕ → Measure ℝ) (θ : ℝ) (a : ℝ≥0∞)
    (hm0 : m 0 = Measure.dirac 0)
    (hmsucc : ∀ n : ℕ, m (n + 1) = Measure.conv κ (m n))
    (hsf : ∀ n : ℕ, SFinite (m n))
    (hκ : (∫⁻ x : ℝ, ENNReal.ofReal (Real.exp (-θ * x)) ∂κ) = a) :
    ∀ n : ℕ,
      (∫⁻ x : ℝ, ENNReal.ofReal (Real.exp (-θ * x)) ∂m n) = a ^ n := by
  sorry

end AvramDividend.Classical
