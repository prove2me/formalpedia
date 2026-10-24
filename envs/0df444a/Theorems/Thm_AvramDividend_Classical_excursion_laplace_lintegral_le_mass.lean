-- Prove2me | Theorems.Thm_AvramDividend_Classical_excursion_laplace_lintegral_le_mass
-- name    : AvramDividend.Classical.excursion_laplace_lintegral_le_mass
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T23:45:28.316987+00:00
-- url     : https://prove2.me/theorems/e1e1a74f-4deb-47f2-ab2f-4f9831b68267
-- title:
--   Laplace transform of a nonnegative-supported measure does not exceed its mass
-- statement:
--   For a measure supported on [0,infinity) and a nonnegative Laplace parameter, the integral of exp(-s x) is at most the total mass. The statement requires no finiteness assumption and supplies an upper bound needed for uniform tightness from reciprocal lower bounds.
-- source:
--   The integrand exp(-s x) is bounded by one almost everywhere on nonnegative support; apply lintegral_mono_ae and lintegral_const.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.ENNReal.Real
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
open MeasureTheory Set
open scoped ENNReal

theorem AvramDividend.Classical.excursion_laplace_lintegral_le_mass
    (μ : Measure ℝ) (s : ℝ) (hs : 0 ≤ s)
    (hsupport : μ (Iio (0 : ℝ)) = 0) :
    (∫⁻ x : ℝ, ENNReal.ofReal (Real.exp (-(s * x))) ∂μ) ≤
      μ Set.univ := by sorry
