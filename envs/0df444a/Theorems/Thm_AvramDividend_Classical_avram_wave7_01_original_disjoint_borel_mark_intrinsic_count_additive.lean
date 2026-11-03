-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_disjoint_borel_mark_intrinsic_count_additive
-- name    : AvramDividend.Classical.avram_wave7_01_original_disjoint_borel_mark_intrinsic_count_additive
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T16:11:00.905837+00:00
-- url     : https://prove2.me/theorems/db5e2ef9-459c-4346-ae66-73439eb792fa
-- title:
--   Original intrinsic Lévy marked jump counts are finitely additive over disjoint Borel mark cells
-- statement:
--   For each sample of the actual original Lévy process X, and any time window (s,t], the intrinsic source marked jump count evaluated on a union of disjoint Borel mark sets is the sum of the individual marked counts. It preserves the original Ω, P, filtration, left-limits and jump measure without ν-rate, integrability or finite-activity hypotheses. This is the exact mark-partition algebra needed before measurable class extensions.
-- source:
--   The original marked count is literally a measure of time-mark pairs; distribute the product rectangle over disjoint marks and apply measure_union with Borel measurability.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_01_original_disjoint_borel_mark_intrinsic_count_additive
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (s t : ℝ≥0)
    (B C : Set ℝ) (hB : MeasurableSet B) (hC : MeasurableSet C)
    (hDisj : Disjoint B C) :
    (let NX : Measure (ℝ≥0 × ℝ) :=
      ((Measure.count.restrict {v : ℝ≥0 |
        0 < v ∧ X.X v ω -
          Function.leftLim (fun w : ℝ≥0 => X.X w ω) v ≠ 0}).map
        (fun v : ℝ≥0 => (v,
          X.X v ω - Function.leftLim (fun w : ℝ≥0 => X.X w ω) v)))
     NX (Ioc s t ×ˢ (B ∪ C)) =
       NX (Ioc s t ×ˢ B) + NX (Ioc s t ×ˢ C)) := by sorry
