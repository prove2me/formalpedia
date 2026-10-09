-- Prove2me | solution 1 for d9_event_indicator_integral_pos_of_subset
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T14:48:32.814547+00:00
-- url     : https://prove2.me/submissions/4a7475bf-fec6-4db4-9863-36aaa4165b67

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open NestedSeatAlloc.IntPolicy
open MeasureTheory ProbabilityTheory in
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (A B : Set Ω) [DecidablePred (fun ω : Ω => ω ∈ B)] (hB : MeasurableSet B)
    (hA : 0 < P.real A) (hAB : A ⊆ B) :
    0 < ∫ ω, (if ω ∈ B then (1 : ℝ) else 0) ∂P := by
  have hindicator :
      (fun ω => if ω ∈ B then (1 : ℝ) else 0) =
        B.indicator (fun _ => (1 : ℝ)) := by
    funext ω
    by_cases hω : ω ∈ B <;> simp [hω]
  have hintegral :
      (∫ ω, (if ω ∈ B then (1 : ℝ) else 0) ∂P) = P.real B := by
    rw [hindicator]
    simpa using (integral_indicator_const (μ := P) (e := (1 : ℝ)) hB)
  rw [hintegral]
  have hmeasure : P.real A ≤ P.real B := by
    change (P A).toReal ≤ (P B).toReal
    exact ENNReal.toReal_mono (measure_ne_top P B) (measure_mono hAB)
  exact lt_of_lt_of_le hA hmeasure
