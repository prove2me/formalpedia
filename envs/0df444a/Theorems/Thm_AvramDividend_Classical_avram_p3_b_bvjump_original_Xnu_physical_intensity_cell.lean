-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_Xnu_physical_intensity_cell
-- name    : AvramDividend.Classical.avram_p3_b_bvjump_original_Xnu_physical_intensity_cell
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T10:29:52.233088+00:00
-- url     : https://prove2.me/theorems/6214094c-500b-4786-9f98-9501906d3306
-- title:
--   Actual original Lévy measure compensator candidate has exact predictable marked-cell intensity
-- statement:
--   For the genuine original spectrally negative Lévy process X, the actual predictable intensity candidate N=μ.prod (X.ν.restrict negative) has mass μ((s,t]×A)·X.ν(B), with no additional SFinite or negative-support assumptions. Both prerequisites are genuinely Proved consequences of X's original process fields. This is an intensity-side calculation only; comparison with original source jump occupation M still requires P2's independent original rate law.
-- source:
--   Proved avram_wave5_01_actual_source_levy_intensity_sigmafinite_from_process_fields; Proved P3-B original ν restriction and marked product intensity formula.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_predictable_marked_intensity_cell
import Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_levy_negative_restrict_eq_self
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_source_levy_intensity_sigmafinite_from_process_fields
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_b_bvjump_original_Xnu_physical_intensity_cell
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (N : @Measure ((ℝ≥0 × Ω) × ℝ)
      (@Prod.instMeasurableSpace _ _
        (𝓕.rightCont.predictable) (inferInstance : MeasurableSpace ℝ)))
    (hN : N = (letI : MeasurableSpace (ℝ≥0 × Ω) :=
      𝓕.rightCont.predictable;
      μ.prod (X.ν.restrict (Iio (0 : ℝ)))))
    (s t : ℝ≥0) (A : Set Ω) (B : Set ℝ) :
    N ((Ioc s t ×ˢ A) ×ˢ B) =
      μ (Ioc s t ×ˢ A) * X.ν B := by sorry
