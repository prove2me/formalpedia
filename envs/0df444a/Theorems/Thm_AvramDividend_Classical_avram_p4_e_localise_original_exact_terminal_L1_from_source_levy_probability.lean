-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_exact_terminal_L1_from_source_levy_probability
-- name    : AvramDividend.Classical.avram_p4_e_localise_original_exact_terminal_L1_from_source_levy_probability
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T16:48:10.376204+00:00
-- url     : https://prove2.me/theorems/4441f5cd-8444-4024-82b9-f1f08ad5a1f4
-- title:
--   Original stopped discounted terminal L1 with probability law derived from native Levy structure
-- statement:
--   At the exact original stopped terminal W and payoff w, the signed budget plus actual L1 residuals and Cash imply terminal L1. The constant initial w x is integrable because the original SpectrallyNegativeLevy source structure contains IsProbabilityMeasure P, without adding an extra finiteness hypothesis. The theorem is a source-faithful strengthening of the previously Proved explicit-constant-L1 helper and leaves the stochastic residual construction to P4-F.
-- source:
--   SpectrallyNegativeLevy.isProbability native source field, previous accepted original exact terminal L1 theorem 10d1b5d9-04dd-4fda-a9fe-e70d5da37bae, and canonical P4-F 0dda1be7-9d8b-41e0-ae51-55fab5c38e22.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_exact_terminal_L1_of_signed_budget_and_initial_constant_L1
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The original Levy process supplies its probability-law witness for the exact terminal budget. -/
theorem AvramDividend.Classical.avram_p4_e_localise_original_exact_terminal_L1_from_source_levy_probability
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
