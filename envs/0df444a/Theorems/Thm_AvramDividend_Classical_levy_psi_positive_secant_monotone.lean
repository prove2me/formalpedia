-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_psi_positive_secant_monotone
-- name    : AvramDividend.Classical.levy_psi_positive_secant_monotone
-- status  : Open
-- author  : @WillR
-- created : 2026-10-21T23:07:15.176521+00:00
-- url     : https://prove2.me/theorems/59b6c198-4db2-4342-a962-bb07246621e6
-- title:
--   Normalised spectrally negative Lévy exponent increases on positive arguments
-- statement:
--   For a spectrally negative Lévy exponent ψ, the normalised chord ψ(θ)/θ from the origin is nondecreasing on θ>0. In Lévy-Khintchine form, the drift contribution c is constant, the Gaussian contribution σ²θ/2 increases, and the normalised compensated negative-jump kernel (exp(θy)-1-θy 1_{(-1,1)}(y))/θ increases pointwise for y<0. The Proved canonical jump integrability result justifies integrating that inequality. This directly provides uniqueness of any strictly positive q-root and the linear lower bound ψ(φ+u)-q≥(q/φ)u, avoiding a full convexity theorem for ψ.
-- source:
--   Lévy-Khintchine exponent; Proved exp_negative_secant_mono, levy_compensated_jump_integrable_nonneg; Mathlib integral_mono_ae.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_exp_negative_secant_mono
import Theorems.Thm_AvramDividend_Classical_levy_compensated_jump_integrable_nonneg
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.levy_psi_positive_secant_monotone
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ₁ θ₂ : ℝ) (hθ₁ : 0 < θ₁) (hθ : θ₁ ≤ θ₂) :
    X.ψ θ₁ / θ₁ ≤ X.ψ θ₂ / θ₂ := by sorry
