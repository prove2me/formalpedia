-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_source_intrinsic_jump_count_time_interval_additive
-- name    : AvramDividend.Classical.avram_wave5_01_actual_source_intrinsic_jump_count_time_interval_additive
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T01:21:34.610195+00:00
-- url     : https://prove2.me/theorems/5658e787-c974-49e2-a139-64c647d22d0e
-- title:
--   Actual source Lévy marked jump counts add exactly over adjacent finite-horizon intervals
-- statement:
--   For any actual sample path of SpectrallyNegativeLevy P 𝓕, measurable signed jump band B, and s≤u≤t, the intrinsic original-path counting measure satisfies N_X((s,t]×B)=N_X((s,u]×B)+N_X((u,t]×B). This is the exact finite-horizon time-slicing identity for stopped source jump sums. It is valid even for infinite activity, with values in ENNReal, and uses neither Poisson intensity nor a detached filtration.
-- source:
--   Original intrinsic source jump measure as count/restrict/map in definition 933ced80-71c1-4c0f-a6a7-ab7757fc97e9 and measure_union on disjoint measurable half-open intervals. Finite-horizon stopped count interface for Chat 02/03.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave5_01_actual_source_intrinsic_jump_count_time_interval_additive
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (s u t : ℝ≥0) (hsu : s ≤ u) (hut : u ≤ t)
    (B : Set ℝ) (hB : MeasurableSet B) :
    ((Measure.count.restrict {v : ℝ≥0 |
      0 < v ∧ X.X v ω - Function.leftLim (fun w : ℝ≥0 => X.X w ω) v ≠ 0}).map
      (fun v : ℝ≥0 => (v,
        X.X v ω - Function.leftLim (fun w : ℝ≥0 => X.X w ω) v))) (Ioc s t ×ˢ B) =
      ((Measure.count.restrict {v : ℝ≥0 |
      0 < v ∧ X.X v ω - Function.leftLim (fun w : ℝ≥0 => X.X w ω) v ≠ 0}).map
      (fun v : ℝ≥0 => (v,
        X.X v ω - Function.leftLim (fun w : ℝ≥0 => X.X w ω) v))) (Ioc s u ×ˢ B) +
      ((Measure.count.restrict {v : ℝ≥0 |
      0 < v ∧ X.X v ω - Function.leftLim (fun w : ℝ≥0 => X.X w ω) v ≠ 0}).map
      (fun v : ℝ≥0 => (v,
        X.X v ω - Function.leftLim (fun w : ℝ≥0 => X.X w ω) v))) (Ioc u t ×ˢ B) := by sorry
