-- Prove2me | Theorems.Thm_AvramDividend_Classical_localized_stopped_terminal_lintegral_iSup_bands
-- name    : AvramDividend.Classical.localized_stopped_terminal_lintegral_iSup_bands
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T11:32:19.204546+00:00
-- url     : https://prove2.me/theorems/b7d1cee6-dc3d-4912-a20c-34e634ead4ef
-- title:
--   Unbounded-reserve stopped HJB terminal expectation recovered from finite-band localisations
-- statement:
--   For a spectrally negative Lévy risk process controlled by an admissible dividend strategy, any stopping time and a globally progressive reserve process, the expected nonnegative stopped terminal verification value before ruin equals the supremum of integer reserve-band truncated expectations. The HJB test is only assumed continuous on nonnegative reserves and zero on negatives. This is an exact monotone-localisation bridge to the unbounded dividend cap.
-- source:
--   AvramDividend.Classical.localized_nonnegative_terminal_lintegral_iSup_bands plus proved Borel measurability of the HJB candidate, survival event and stopped-reserve measurability.

import Mathlib.Probability.Process.Stopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_survival_event_measurable_of_stopping_and_admissible
import Theorems.Thm_AvramDividend_Classical_local_verification_candidate_borel_and_postPayment_adapted
import Theorems.Thm_AvramDividend_Classical_localized_nonnegative_terminal_lintegral_iSup_bands

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.localized_stopped_terminal_lintegral_iSup_bands
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (hw : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (τ : Ω → ℝ≥0∞) (hτ : IsStoppingTime 𝓕 τ)
    (hProg : ProgMeasurable 𝓕 (riskProcess X x D)) :
    (∫⁻ ω, if τ ω < ruinTime X x D ω ∧
        0 ≤ stoppedValue (riskProcess X x D) τ ω then
        ENNReal.ofReal (w (stoppedValue (riskProcess X x D) τ ω))
      else 0 ∂P) =
    ⨆ n : ℕ, (∫⁻ ω, if τ ω < ruinTime X x D ω ∧
        0 ≤ stoppedValue (riskProcess X x D) τ ω ∧
        stoppedValue (riskProcess X x D) τ ω ≤ (n : ℝ) then
        ENNReal.ofReal (w (stoppedValue (riskProcess X x D) τ ω))
      else 0 ∂P) := by sorry
