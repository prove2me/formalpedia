-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_finite_cap_stopped_terminal_integrable
-- name    : AvramDividend.Classical.avram_p4_f_assembly_original_finite_cap_stopped_terminal_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T09:03:20.72317+00:00
-- url     : https://prove2.me/theorems/2d3eb5aa-fc7a-4d85-afea-b08fc93dc11e
-- title:
--   Genuine original stopped discounted terminal is automatically L1 under finite real cap and canonical continuity
-- statement:
--   The actual canonical postpayment-or-ruin W lies below the finite admissible real cap by a separately accepted original-source lemma. Canonical ContinuousOn w (Ici 0) plus zero extension on negatives bounds w uniformly on all W, including ruin overshoot. Applying accepted P4-E terminal integrability to the given original AEStronglyMeasurable exact Term yields Integrable Term on X's own probability law, with no new integrability assumption. No claim is made for infinite cap or the source Ito formula.
-- source:
--   Accepted P4-F finite-cap zero-extended verification bound, P4-F source stopped cap, P4-E 782559c6 discounted terminal integrable_of_ae_bound.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_zero_extended_continuous_value_bounded_on_finite_cap
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_finite_cap_stopped_terminal_reserve_le
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_discounted_terminal_integrable_of_ae_bound
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f_assembly_original_finite_cap_stopped_terminal_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 ≤ q)
    (w : ℝ → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (x : ℝ) (hxc : ENNReal.ofReal x ≤ ENNReal.ofReal c)
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x (ENNReal.ofReal c) D)
    (τ : Ω → ℝ≥0) (W Term : Ω → ℝ)
    (hW : ∀ ω, W ω =
      if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω then
        x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω)
    (hTerm : ∀ ω, Term ω =
      Real.exp (-(q * (τ ω : ℝ))) * w (W ω))
    (hTermMeas : AEStronglyMeasurable Term P) :
    Integrable Term P := by sorry
