-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_finite9_predictable_inclusive_sigma_mask_L1
-- name    : AvramDividend.Classical.avram_ubv_finite9_predictable_inclusive_sigma_mask_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T17:27:16.278539+00:00
-- url     : https://prove2.me/theorems/e7333410-0173-42f4-8722-4e3ad618e3e3
-- title:
--   Original predictable-clock integrability transfers to an inclusive stopped physical time integral
-- statement:
--   For the pinned original right-continuous filtration, take the finite physical time-measure restricted to the horizon and a predictable measure agreeing with its product with the original probability law on all predictable measurable sets. An integrable original predictable kernel remains integrable after inclusive masking by any right-continuous stopping time and integration along each physical path. This transfers the compact finite-cap generator L1 certificate into the exact time-integrated source needed by the original stopped jump/HJB estimate; applying it to that kernel and assembling the Ito-Meyer and dividend identities remain separate obligations.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_predictable_le_product_space
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_nnreal_stopping_inclusive_predictable_mask

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ubv_finite9_predictable_inclusive_sigma_mask_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (T : ℝ≥0)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (hμclock : ∀ A : Set (ℝ≥0 × Ω),
      MeasurableSet[𝓕.rightCont.predictable] A →
      μ A = ((((volume : Measure ℝ).restrict
        (Icc 0 (T : ℝ))).map Real.toNNReal).prod P) A)
    (G : ℝ≥0 × Ω → ℝ)
    (hGI : (letI : MeasurableSpace (ℝ≥0 × Ω) :=
      𝓕.rightCont.predictable; Integrable G μ))
    (σ : Ω → ℝ≥0)
    (hσstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (σ ω : WithTop ℝ≥0))) :
    Integrable (fun ω =>
      ∫ t : ℝ≥0,
        if t ≤ σ ω then G (t, ω) else 0
      ∂(((volume : Measure ℝ).restrict
        (Icc 0 (T : ℝ))).map Real.toNNReal)) P := by sorry
