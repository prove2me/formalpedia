-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_exact_terminal_L1_from_source_signed_budget
-- name    : AvramDividend.Classical.avram_p4_e_localise_original_exact_terminal_L1_from_source_signed_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T16:08:05.337871+00:00
-- url     : https://prove2.me/theorems/9fae7ffc-4253-438f-841c-f050e18a454a
-- title:
--   Exact original stopped UBV terminal is L¹ after the integrable signed residual budget
-- statement:
--   From the certified source interior gradient and w(0)≥0 obtain allcap nonnegative capped payoff, then the certified stopped original W and negative extension obtain Term≥0 in all horizon and ruin branches. The assumed integrable M,G,H,Cash signed residual budget dominates Term by an integrable random variable, proving genuine Term L1 without local-martingale optional stopping or a terminal integrability premise.
-- source:
--   Accepted original capped payoff positivity 79db013c-9a6c-4ff2-9410-2e3bf66ca8a0 and exact W terminal sign 42338799-ddde-4ad7-9e0a-2f18bea6761e, plus original P4-F budget interface.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_anycap_payoff_nonnegative_from_source_interior_gradient
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_discounted_terminal_nonnegative_of_cap_payoff_sign
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The exact source signed stopped budget forces terminal L¹ from its sign and integrable M,G,H,Cash. -/
theorem AvramDividend.Classical.avram_p4_e_localise_original_exact_terminal_L1_from_source_signed_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (hxc : ENNReal.ofReal x ≤ C)
    (q : ℝ) (τ : Ω → ℝ≥0) (W : Ω → ℝ)
    (hW : ∀ ω, W ω =
      if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
      then x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω)
    (w : ℝ → ℝ) (hw0 : 0 ≤ w 0)
    (hwCont : ContinuousOn w (Ici (0 : ℝ)))
    (hwNeg : ∀ y : ℝ, y < 0 → w y = 0)
    (hwSmooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hwGrad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (Term Cash M G H : Ω → ℝ)
    (hTerm : ∀ ω, Term ω =
      Real.exp (-(q * (τ ω : ℝ))) * w (W ω))
    (hTermMeas : AEStronglyMeasurable Term P)
    (hCashI : Integrable Cash P)
    (hMI : Integrable M P) (hGI : Integrable G P)
    (hHI : Integrable H P)
    (hBudget : ∀ᵐ ω ∂P,
      Term ω + Cash ω ≤ w x + M ω + G ω + H ω) :
    Integrable Term P := by sorry
