-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_top9_predictable_integrable_physical_time_fibre_sfinite
-- name    : AvramDividend.Classical.avram_ubv_top9_predictable_integrable_physical_time_fibre_sfinite
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T09:55:30.002784+00:00
-- url     : https://prove2.me/theorems/a5a26c4d-25d7-4478-902a-8b1fbe3ffc16
-- title:
--   S-finite physical-time fibre integrability from predictable product measure law
-- statement:
--   For a s-finite source probability law and genuine finite physical clock, the predictable-space integrable stopped source R is Bochner-integrable after physical-time integration. The s-finiteness condition supplies the Fubini/Tonelli instance omitted in the original unrestricted-measure statement; real Lévy laws are probabilities.
-- source:
--   Correction of avram_ubv_top9_predictable_integrable_physical_time_fibre. Reuse proved argument of avram_ubv_top9_original_law_integrable_predictable_time_fibre with unnecessary X variable replaced by SFinite P.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ubv_top9_predictable_integrable_physical_time_fibre_sfinite
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [SFinite P]
    {𝓕 : Filtration ℝ≥0 mΩ}
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
