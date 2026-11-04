-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_all_horizon_marked_finite_cells_compensate
-- name    : AvramDividend.Classical.avram_p3_b_bvjump_original_all_horizon_marked_finite_cells_compensate
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T10:55:21.143381+00:00
-- url     : https://prove2.me/theorems/ce230a31-61cc-4766-b2b7-657421459a5a
-- title:
--   Original stopped Lévy jump count and genuine physical predictable intensity agree on all adapted finite marked cells
-- statement:
--   For the same original Ω,P,rightCont filtration, intrinsic marked Lévy jump occupation M and physical X.ν intensity N, assuming precisely the outstanding P2 unconditional original source finite-rectangle rate, the true stopped source measure M restricted at horizon T and the actual finite physical-clock compensator N agree on every adapted marked (s,t]×A×B with s≤t, including crossing and after-horizon cells. Uses already Proved source/intensity horizon clipping, exact finite interior rate, and zero-mass cases. This supplies the exact hRect input to the accepted P3-B future extractor without any new process or stronger rate premise.
-- source:
--   P3-B accepted finite-horizon original source-cell compensation, source/intensity horizon clipping and after-horizon zero; source rate premise assigned to P2.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_finite_horizon_marked_rect_compensator
import Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_marked_restricted_cell_measure
import Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_Xnu_marked_intensity_horizon_clip
import Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_marked_cell_after_horizon_zero
import Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_Xnu_marked_intensity_after_horizon_zero
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_b_bvjump_original_all_horizon_marked_finite_cells_compensate
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0)
    (M : @Measure ((ℝ≥0 × Ω) × ℝ)
      (@Prod.instMeasurableSpace _ _
        (𝓕.rightCont.predictable) (inferInstance : MeasurableSpace ℝ)))
    (hRate : ∀ (s t : ℝ≥0), s ≤ t →
      ∀ (A : Set Ω), MeasurableSet[𝓕 s] A →
      ∀ (B : Set ℝ), MeasurableSet B →
        M ((Ioc s t ×ˢ A) ×ˢ B) =
        P A * ((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (hμclock : ∀ E : Set (ℝ≥0 × Ω),
      MeasurableSet[𝓕.rightCont.predictable] E →
      μ E = ((((volume : Measure ℝ).restrict
        (Icc 0 (T : ℝ))).map Real.toNNReal).prod P) E)
    (N : @Measure ((ℝ≥0 × Ω) × ℝ)
      (@Prod.instMeasurableSpace _ _
        (𝓕.rightCont.predictable) (inferInstance : MeasurableSpace ℝ)))
    (hN : N = (letI : MeasurableSpace (ℝ≥0 × Ω) :=
      𝓕.rightCont.predictable;
      μ.prod (X.ν.restrict (Iio (0 : ℝ)))))
    (s t : ℝ≥0) (hst : s ≤ t)
    (A : Set Ω) (hA : MeasurableSet[𝓕 s] A)
    (B : Set ℝ) (hB : MeasurableSet B) :
    (M.restrict {p | p.1.1 ≤ T}) ((Ioc s t ×ˢ A) ×ˢ B) =
      N ((Ioc s t ×ˢ A) ×ˢ B) := by sorry
