-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_finite_clock_Xnu_marked_cell_rate
-- name    : AvramDividend.Classical.avram_p3_b_bvjump_original_finite_clock_Xnu_marked_cell_rate
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T10:36:32.453552+00:00
-- url     : https://prove2.me/theorems/500c4658-a03a-4981-b485-2f9d33f83985
-- title:
--   Original physical finite-clock marked Lévy intensity evaluates exactly on adapted rectangles
-- statement:
--   On the genuine original Ω/P/rightCont filtration, the canonical finite predictable clock μ and original X.ν intensity N=μ.prod X.ν(restrict negative) evaluate every adapted marked (s,t]×A×B inside [0,T] as ENNReal.ofReal(t-s)·P(A)·X.ν(B). Uses only physical-clock and source-ν structural facts, without a source compensator assumption. Combining this with P2's original NX count rate is the exact M=N rectangle step required by P3's accepted finite-cell-to-future helper.
-- source:
--   Accepted P3-B source intensity product and true original predictable physical clock interval-event mass, plus original X.ν support and sigma-finiteness.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_Xnu_physical_intensity_cell
import Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_predictable_clock_interval_event_mass
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_b_bvjump_original_finite_clock_Xnu_marked_cell_rate
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
    (s t : ℝ≥0) (htT : t ≤ T)
    (A : Set Ω) (hA : MeasurableSet[𝓕 s] A)
    (B : Set ℝ) :
    N ((Ioc s t ×ˢ A) ×ˢ B) =
      (ENNReal.ofReal ((t : ℝ) - (s : ℝ)) * P A) * X.ν B := by sorry
