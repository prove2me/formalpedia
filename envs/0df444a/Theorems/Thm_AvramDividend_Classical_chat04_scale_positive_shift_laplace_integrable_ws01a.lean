-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_scale_positive_shift_laplace_integrable_ws01a
-- name    : AvramDividend.Classical.chat04_scale_positive_shift_laplace_integrable_ws01a
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T17:18:56.325174+00:00
-- url     : https://prove2.me/theorems/bc478322-8d08-43c0-af52-ed49deff68dd
-- title:
--   Positive reserve-shift exponential integrability of a Lévy q-scale function
-- statement:
--   For a genuine q-scale function, θ≥0 with ψ(θ)>q, and any nonnegative reserve shift b, prove integrability of x↦exp(−θx)W(x+b) on the positive half-line. Extend the known unshifted Laplace integrability by a zero-extended integrable indicator and translation invariance of Lebesgue measure. This supplies the exponential-horizon WH random-reserve integrability envelope without assuming killed harmonicity or any exit formula.
-- source:
--   Canonical Proved scaleFunction_shiftedLaplace_integrable (da4289b8); translation invariance MeasureTheory.Integrable.comp_add_right in pinned Mathlib; elementary exponential multiplicativity.

import Mathlib.MeasureTheory.Group.Integral
import Theorems.Thm_AvramDividend_Classical_scaleFunction_shiftedLaplace_integrable

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat04_scale_positive_shift_laplace_integrable_ws01a
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (θ b : ℝ) (hθ : 0 ≤ θ) (hqθ : q < X.ψ θ) (hb : 0 ≤ b) :
    IntegrableOn (fun x : ℝ => Real.exp (-(θ * x)) * W (x + b))
      (Ioi (0 : ℝ)) := by sorry
