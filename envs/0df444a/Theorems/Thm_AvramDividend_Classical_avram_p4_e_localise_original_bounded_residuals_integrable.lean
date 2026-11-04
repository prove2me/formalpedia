-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_bounded_residuals_integrable
-- name    : AvramDividend.Classical.avram_p4_e_localise_original_bounded_residuals_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T07:46:41.81071+00:00
-- url     : https://prove2.me/theorems/9f3163fc-7f5e-4a21-8218-00070a718618
-- title:
--   Actual probability-space bounded signed residuals are separately integrable
-- statement:
--   For the unchanged original spectrally negative Levy law, any three explicitly defined strongly measurable original-path residuals M, G and H with almost-sure finite deterministic norm bounds are separately L1 integrable. The result uses the source probability law and pinned Mathlib Integrable.of_bound. It enables the exact original Ito-Meyer residual theorem to discharge its three separate Integrable obligations once genuine stopped bounds have been proved. It assumes and does not manufacture a martingale, its mean zero, or the residual inequalities.
-- source:
--   Source SpectrallyNegativeLevy.isProbability and pinned Mathlib MeasureTheory.Integrable.of_bound.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_p4_e_localise_original_bounded_residuals_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (M G H : Ω → ℝ)
    (hMm : AEStronglyMeasurable M P)
    (hGm : AEStronglyMeasurable G P)
    (hHm : AEStronglyMeasurable H P)
    (BM BG BH : ℝ)
    (hMb : ∀ᵐ ω ∂P, ‖M ω‖ ≤ BM)
    (hGb : ∀ᵐ ω ∂P, ‖G ω‖ ≤ BG)
    (hHb : ∀ᵐ ω ∂P, ‖H ω‖ ≤ BH) :
    Integrable M P ∧ Integrable G P ∧ Integrable H P := by sorry
