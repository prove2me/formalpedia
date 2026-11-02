-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_ubv_original_ito_terminal_piecewise_reward_nonneg
-- name    : AvramDividend.Classical.avram_wave7_ubv_original_ito_terminal_piecewise_reward_nonneg
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T19:37:48.149343+00:00
-- url     : https://prove2.me/theorems/0eb5420e-1c79-4d2e-b7d1-f3030b0bf5e7
-- title:
--   Original UBV piecewise stopped Ito terminal reward nonnegative under exact Chat 06 W and Term definitions
-- statement:
--   For the actual original spectrally negative Levy X and admissible D under the corrected UBV w assumptions, take the exact same piecewise terminal reward W as the Open Chat 06 expected-budget theorem b02af371-7a57-4d30-9a67-a2a03ebab34b: before ruin W is x+X_tau-rightLimit D_tau, otherwise W is riskProcess at tau. With Term=exp(-q tau)*w(W), Term is nonnegative P-almost surely. Reuse the two accepted all-cap original terminal and postpayment candidate nonnegativity theorems and positivity of the discount factor. This directly discharges Chat 06's hTermNonneg without extra boundary smoothness, zero local-time assumptions, finite-cap restrictions or controlled Ito-Meyer integration.
-- source:
--   Exact Open Chat 06 expected-budget assembly b02af371-7a57-4d30-9a67-a2a03ebab34b; accepted original prepayment terminal sign c7bf9b3b-8066-4109-a2fc-b9ac81e3ca0f and postpayment sign 06839544-2429-48b2-bce8-78e4b76dd814.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave7_ubv_original_ito_terminal_piecewise_reward_nonneg
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
    (τ : Ω → ℝ≥0) (W Term : Ω → ℝ)
    (hW : ∀ ω, W ω =
      if (τ ω : ℝ≥0∞) < ruinTime X x D ω then
        x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω)
    (hTerm : ∀ ω,
      Term ω = Real.exp (-(q * (τ ω : ℝ))) * w (W ω)) :
    ∀ᵐ ω ∂P, 0 ≤ Term ω := by sorry
