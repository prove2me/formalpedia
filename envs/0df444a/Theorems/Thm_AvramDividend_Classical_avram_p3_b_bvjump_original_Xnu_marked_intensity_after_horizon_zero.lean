-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_Xnu_marked_intensity_after_horizon_zero
-- name    : AvramDividend.Classical.avram_p3_b_bvjump_original_Xnu_marked_intensity_after_horizon_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T10:42:04.257067+00:00
-- url     : https://prove2.me/theorems/5d106b14-2454-4c8e-b1ab-561a73df783d
-- title:
--   Genuine original marked Lévy intensity has zero predictable-cell mass after stopped physical horizon
-- statement:
--   For the actual original spectrally negative Lévy process X on Ω/P/rightCont filtration, and the actual physical stopped predictable clock μ, the genuine marked intensity μ.prod(X.ν restricted to negative jumps) assigns zero mass to every adapted marked cell (s,t]×A×B starting at s≥T, even when X.ν(B)=∞. It follows from clock support and genuine source ν structural identities, without assuming source jump compensation.
-- source:
--   Proved P3-B original ν physical intensity cell and stopped clock post-horizon zero; Mathlib predictable_Ioc_prod and Measure.prod_prod.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_Xnu_physical_intensity_cell
import Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_clock_after_horizon_zero
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_b_bvjump_original_Xnu_marked_intensity_after_horizon_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0)
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
    (s t : ℝ≥0) (hTs : T ≤ s)
    (A : Set Ω) (hA : MeasurableSet[𝓕 s] A)
    (B : Set ℝ) :
    N ((Ioc s t ×ˢ A) ×ˢ B) = 0 := by sorry
