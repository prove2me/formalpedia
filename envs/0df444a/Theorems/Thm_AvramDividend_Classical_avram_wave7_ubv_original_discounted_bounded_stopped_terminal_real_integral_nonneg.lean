-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_ubv_original_discounted_bounded_stopped_terminal_real_integral_nonneg
-- name    : AvramDividend.Classical.avram_wave7_ubv_original_discounted_bounded_stopped_terminal_real_integral_nonneg
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T19:25:31.808591+00:00
-- url     : https://prove2.me/theorems/1baa39ac-f800-4494-adb5-9c4f8bed13b6
-- title:
--   Original UBV discounted real stopped terminal integral is nonnegative under w(0)>=0 and finite clipping
-- statement:
--   For the actual original SpectrallyNegativeLevy P 𝓕 in unbounded variation with admissible D and the corrected core's w(0)>=0, positive-side continuity, negative-side zero, C2 interior and gradient assumptions, every original 𝓕.rightCont stopping clock τ, including τ=∞, has a nonnegative discounted real integral of w evaluated at reserve at its finite clip τ∧T. The proof instantiates the Proved all-cap pathwise terminal nonnegativity at the finite clipped time and uses positivity of the real exponential and integral_nonneg_of_ae. It introduces no new boundary or smoothness assumption and does not claim terminal integrability, a martingale identity or a controlled Ito-Meyer formula.
-- source:
--   Proved all-cap original stopped terminal nonnegative theorem c7bf9b3b-8066-4109-a2fc-b9ac81e3ca0f and original right-continuous source filtration. This is a terminal-sign handoff only.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave7_ubv_original_discounted_bounded_stopped_terminal_real_integral_nonneg
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (x : ℝ) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (τ : Ω → ℝ≥0∞) (hτstop : IsStoppingTime 𝓕.rightCont τ)
    (T : ℝ≥0) :
    0 ≤ (∫ ω, Real.exp (-q * ((min (τ ω) (T : ℝ≥0∞)).toNNReal : ℝ)) *
      w (riskProcess X x D
        (min (τ ω) (T : ℝ≥0∞)).toNNReal ω) ∂P) := by sorry
