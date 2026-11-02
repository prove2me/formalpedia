-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_ubv_original_piecewise_stopped_terminal_positivepart_lintegral_bound
-- name    : AvramDividend.Classical.avram_wave7_ubv_original_piecewise_stopped_terminal_positivepart_lintegral_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T19:44:23.4632+00:00
-- url     : https://prove2.me/theorems/ea19d5ed-4d0a-47c6-9f12-3cd1496d9860
-- title:
--   Original UBV Chat 06 piecewise discounted stopped positive-part expectation domination
-- statement:
--   For the genuine original spectrally negative Lévy process, unchanged right-continuous filtration, actual admissible dividend strategy D and the exact pre-ruin/post-ruin reward W used in the open Chat 06 Ito budget theorem, prove that the ENNReal expectation of exp(-q tau)*max(0,W) is bounded above by the ENNReal expectation of exp(-q tau)*w(W). Retain Chat 06's bounded source stopping-clock assumptions. Zero ruin, creeping, overshoot, and all cap endpoints are included. Neither integrability nor Ito/Meyer/Stieltjes identities is inferred.
-- source:
--   Original Chat 06 expected budget theorem b02af371-7a57-4d30-9a67-a2a03ebab34b; original Proved all-cap positive-part theorems 2b04d61b-0c38-44e4-ba16-ea6843d0c45e and 9ae5dedd-b82e-4205-9f96-af361b8e4e08.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_ubv_original_allcap_terminal_positive_part_domination
import Theorems.Thm_AvramDividend_Classical_avram_wave6_ubv_original_allcap_postpayment_positive_part_domination

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave7_ubv_original_piecewise_stopped_terminal_positivepart_lintegral_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (x : ℝ) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (τ : Ω → ℝ≥0) (T : ℝ≥0)
    (hτBound : ∀ ω, τ ω ≤ T)
    (hτ : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (hτruin : ∀ ω, (τ ω : ℝ≥0∞) ≤ ruinTime X x D ω)
    (W : Ω → ℝ)
    (hW : ∀ ω, W ω =
      if (τ ω : ℝ≥0∞) < ruinTime X x D ω then
        x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω) :
    (∫⁻ ω, ENNReal.ofReal (
      Real.exp (-(q * (τ ω : ℝ))) * max 0 (W ω)) ∂P) ≤
    (∫⁻ ω, ENNReal.ofReal (
      Real.exp (-(q * (τ ω : ℝ))) * w (W ω)) ∂P) := by sorry
