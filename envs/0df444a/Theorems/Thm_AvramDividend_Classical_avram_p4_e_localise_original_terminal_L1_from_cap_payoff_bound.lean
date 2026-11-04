-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_terminal_L1_from_cap_payoff_bound
-- name    : AvramDividend.Classical.avram_p4_e_localise_original_terminal_L1_from_cap_payoff_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T15:15:08.76308+00:00
-- url     : https://prove2.me/theorems/25d93d26-ab35-4190-9149-b702b3047347
-- title:
--   Original ruin/survival terminal globally L¹ under a genuine uniform bound on w over admissible cap states
-- statement:
--   Use the exactly original W terminal state and admissibility at both τ=0/survival and positive ruin to ensure ENNReal.ofReal W≤C. If W<0 the required source negative extension w=0 applies; otherwise the explicit cap-range payoff bound controls |w(W)|. A previous accepted original discounted-terminal lemma gives global L1 for q≥0. No zero occupation, martingale UI or hidden boundedness of w follows merely from interior C2; hwCap remains an explicit checkable assumption.
-- source:
--   Accepted P4-E original terminal cap invariant 0fe5d1ab, accepted P4-E discounted bounded terminal 782559c6, source hw_neg.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_terminal_reserve_cap_even_at_ruin
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_discounted_terminal_integrable_of_ae_bound
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The actual stopped W with a cap-range bound yields an integrable original discounted terminal. -/
theorem AvramDividend.Classical.avram_p4_e_localise_original_terminal_L1_from_cap_payoff_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (hxc : ENNReal.ofReal x ≤ C)
    (q : ℝ) (hq : 0 ≤ q)
    (τ : Ω → ℝ≥0) (W : Ω → ℝ)
    (hW : ∀ ω, W ω =
      if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
      then x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω)
    (w : ℝ → ℝ) (hwneg : ∀ y : ℝ, y < 0 → w y = 0)
    (B : ℝ) (hB : 0 ≤ B)
    (hwCap : ∀ y : ℝ, 0 ≤ y → ENNReal.ofReal y ≤ C → |w y| ≤ B)
    (hMeas : AEStronglyMeasurable
      (fun ω => Real.exp (-(q * (τ ω : ℝ))) * w (W ω)) P) :
    Integrable (fun ω => Real.exp (-(q * (τ ω : ℝ))) * w (W ω)) P := by sorry
