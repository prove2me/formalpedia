-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_exact_terminal_L1_of_signed_budget_and_initial_constant_L1
-- name    : AvramDividend.Classical.avram_p4_e_localise_original_exact_terminal_L1_of_signed_budget_and_initial_constant_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T16:22:20.842926+00:00
-- url     : https://prove2.me/theorems/10d1b5d9-04dd-4fda-a9fe-e70d5da37bae
-- title:
--   Original exact discounted terminal L1 from signed budget and explicitly integrable source initial constant
-- statement:
--   Given genuine original source cap, C² and derivative hypotheses, certified allcap payoff and stopped W sign make Term≥0 even at ruin. A real signed stopped budget bounded above by w x+M+G+H-Cash implies Term L1 when M,G,H,Cash and the initial constant random variable are all explicitly Integrable. The constant-integrability premise is essential if the arbitrary source measure P is not yet known to be finite; no hidden probability instance is assumed.
-- source:
--   Accepted cap payoff 79db013c, source terminal sign 42338799 and exact P4-F signed budget; explicit hConstI avoids non-inferred finite measure.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_anycap_payoff_nonnegative_from_source_interior_gradient
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_discounted_terminal_nonnegative_of_cap_payoff_sign
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The exact source signed stopped budget forces terminal L¹ from its sign and integrable M,G,H,Cash. -/
theorem AvramDividend.Classical.avram_p4_e_localise_original_exact_terminal_L1_of_signed_budget_and_initial_constant_L1
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
    (hConstI : Integrable (fun _ : Ω => w x) P)
    (hCashI : Integrable Cash P)
    (hMI : Integrable M P) (hGI : Integrable G P)
    (hHI : Integrable H P)
    (hBudget : ∀ᵐ ω ∂P,
      Term ω + Cash ω ≤ w x + M ω + G ω + H ω) :
    Integrable Term P := by sorry
