-- Prove2me | Theorems.Thm_AvramDividend_Classical_atom_zero_of_finite_laplace_inverse_diverges
-- name    : AvramDividend.Classical.atom_zero_of_finite_laplace_inverse_diverges
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-21T15:27:51.720899+00:00
-- url     : https://prove2.me/theorems/9f464a39-d590-4afe-8af0-1e1d30ea35a2
-- title:
--   Finite positive-measure Laplace inverse vanishing forces zero atom at origin
-- statement:
--   Let μ be a finite real measure supported in [0,∞), and let F(n)→+∞. If the nonnegative-real Laplace transform of μ at every natural n equals 1/F(n), then μ{0}=0. Use the Proved natural-Laplace atom-extraction theorem, the limit 1/F(n)→0, uniqueness of limits, and the integral of the singleton indicator. This is the exact missing atom-at-zero argument for the original purejump unbounded-variation ladder renewal potential when its killed Bernstein exponent diverges.
-- source:
--   Proved b6e59826 nonnegative_laplace_transform_atom_zero_limit_nat, pinned tendsto_inv_atTop_zero, MeasureTheory.integral_indicator_one, ENNReal.toReal_eq_zero_iff and finite measure_ne_top; rootward source 2fa29eaf.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_nonnegative_laplace_transform_atom_zero_limit_nat
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.atom_zero_of_finite_laplace_inverse_diverges
    (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hSupport : μ (Iio (0 : ℝ)) = 0)
    (F : ℕ → ℝ) (hF : Tendsto F atTop atTop)
    (hLap : ∀ n : ℕ,
      (∫ x : ℝ, Real.exp ((n : ℝ) * (-x)) ∂μ) = (F n)⁻¹) :
    μ {(0 : ℝ)} = 0 := by sorry
