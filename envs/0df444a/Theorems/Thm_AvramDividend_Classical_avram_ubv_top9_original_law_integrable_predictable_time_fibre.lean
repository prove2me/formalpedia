-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_top9_original_law_integrable_predictable_time_fibre
-- name    : AvramDividend.Classical.avram_ubv_top9_original_law_integrable_predictable_time_fibre
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T22:23:34.795435+00:00
-- url     : https://prove2.me/theorems/5986fea6-8562-4744-8464-de2564da5a0d
-- title:
--   True original Lévy probability law transfers predictable-clock integrability to physical-time fibres
-- statement:
--   For the actual spectrally negative Lévy process, whose structure carries IsProbabilityMeasure P, an integrable right-continuous predictable integrand remains integrable after taking the finite-horizon physical-time integral for each sample point. The predictable clock agrees with Lebesgue time times the original P on every predictable event. This is a source-compatible probability-law specialisation of Open 53f00d00, required for source-exact Itô–Meyer localisation.
-- source:
--   Original physical-clock hμeq as in 53f00d00; X.isProbability is a field of the authoritative SpectrallyNegativeLevy definition used by 25573e81. Pinned Mathlib integrable_of_integrable_trim and Integrable.integral_prod_right, with the accepted predictable inclusion proof from 55a364af. No new assumption is added to the original-process target 25573e81.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ubv_top9_original_law_integrable_predictable_time_fibre
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (R : ℝ≥0 × Ω → ℝ)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (hμeq : ∀ A : Set (ℝ≥0 × Ω),
      MeasurableSet[𝓕.rightCont.predictable] A →
      μ A = ((((volume : Measure ℝ).restrict
        (Icc 0 (T : ℝ))).map Real.toNNReal).prod P) A)
    (hR : Integrable R μ) :
    Integrable (fun ω : Ω =>
      ∫ t : ℝ≥0, R (t, ω) ∂
        (((volume : Measure ℝ).restrict
          (Icc 0 (T : ℝ))).map Real.toNNReal)) P := by sorry
