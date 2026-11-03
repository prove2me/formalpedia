-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_past_weighted_mark_occupation_time_additive
-- name    : AvramDividend.Classical.avram_wave7_01_original_past_weighted_mark_occupation_time_additive
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T15:28:35.015913+00:00
-- url     : https://prove2.me/theorems/72838ed3-df99-447b-995b-a7ee19ef7e9c
-- title:
--   Past-event weighted original Lévy marked occupation is time-additive for arbitrary Borel marks
-- statement:
--   For the original Lévy process and any past event A measurable at s, construct its genuine expected marked occupation measure Q with Q(C)=E_P[1_A N_X(C)] on all Borel time–mark sets, and prove exact Q additivity on consecutive physical rectangles (s,t]×B and (t,u]×B for arbitrary ordered s≤t≤u and Borel B. This is a source-faithful weighted jump-count first-moment time-additivity interface, valid under infinite jump activity.
-- source:
--   Use the Proved original event-weighted expected occupation-measure construction e509ef60-0d03-429a-a727-37c8bc8f1865 and the measure_union identity for adjacent disjoint time–mark rectangles.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_01_original_past_expected_time_mark_occupation_measure

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_01_original_past_weighted_mark_occupation_time_additive
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t u : ℝ≥0) (hst : s ≤ t) (htu : t ≤ u)
    (A : Set Ω) (hA : MeasurableSet[𝓕 s] A)
    (B : Set ℝ) (hB : MeasurableSet B) :
    ∃ Q : Measure (ℝ≥0 × ℝ),
      (∀ C : Set (ℝ≥0 × ℝ), MeasurableSet C →
        Q C = (∫⁻ ω in A, ((Measure.count.restrict {v : ℝ≥0 |
          0 < v ∧ X.X v ω -
            Function.leftLim (fun w : ℝ≥0 => X.X w ω) v ≠ 0}).map
          (fun v : ℝ≥0 => (v,
            X.X v ω - Function.leftLim (fun w : ℝ≥0 => X.X w ω) v))) C ∂P)) ∧
      Q (Ioc s u ×ˢ B) =
        Q (Ioc s t ×ˢ B) + Q (Ioc t u ×ˢ B) := by sorry
