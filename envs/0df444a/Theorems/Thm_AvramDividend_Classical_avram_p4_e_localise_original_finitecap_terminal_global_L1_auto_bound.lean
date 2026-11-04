-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_finitecap_terminal_global_L1_auto_bound
-- name    : AvramDividend.Classical.avram_p4_e_localise_original_finitecap_terminal_global_L1_auto_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T15:30:17.55311+00:00
-- url     : https://prove2.me/theorems/d5ea6491-4a05-4ade-a774-84b206d3d13d
-- title:
--   True finite-cap original terminal Integrable from the source continuity and negative overshoot extension alone
-- statement:
--   Under literal P4-F W, X and original cap-admissibility, finite cap C=ENNReal.ofReal c yields a pathwise upper bound on W even at positive ruin, while w(y)=0 for overshoots below zero. The source hw_cont on Ici 0 yields compact uniform boundedness on [0,c], so the exact discounted terminal is globally L1 whenever it has the original P4-F AEStronglyMeasurable witness. No extra uniform payoff-bound assumption, zero-occupation hypothesis, optional-stopping argument or C2 extension across 0 is needed; C=top remains outside scope.
-- source:
--   Accepted/queued source P4-E exact terminal reserve cap, finite-cap extreme value bound, and bounded-discount terminal global L1 composition.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_finitecap_continuous_payoff_uniform_bound
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_terminal_L1_from_cap_payoff_bound
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The true original finite-cap ruin/survival terminal is globally L¹ from exactly half-line continuity and negative extension. -/
theorem AvramDividend.Classical.avram_p4_e_localise_original_finitecap_terminal_global_L1_auto_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x c : ℝ) (hc : 0 ≤ c)
    (hxc : ENNReal.ofReal x ≤ ENNReal.ofReal c)
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x (ENNReal.ofReal c) D)
    (q : ℝ) (hq : 0 ≤ q)
    (τ : Ω → ℝ≥0) (W : Ω → ℝ)
    (hW : ∀ ω, W ω =
      if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
      then x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω)
    (w : ℝ → ℝ) (hwcont : ContinuousOn w (Ici 0))
    (hwneg : ∀ y : ℝ, y < 0 → w y = 0)
    (hMeas : AEStronglyMeasurable
      (fun ω => Real.exp (-(q * (τ ω : ℝ))) * w (W ω)) P) :
    Integrable (fun ω => Real.exp (-(q * (τ ω : ℝ))) * w (W ω)) P := by sorry
