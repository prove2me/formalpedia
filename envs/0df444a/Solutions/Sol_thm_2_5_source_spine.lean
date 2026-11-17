-- Prove2me | solution 1 for thm_2_5_source_spine
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T22:03:46.023776+00:00
-- url     : https://prove2.me/submissions/5e547e19-2425-4507-813b-68e89dfc1b13

import Theorems.Thm_thm_2_4
import Theorems.Thm_thm_2_5_gap_iUnion_eq
import Theorems.Thm_thm_2_5_gap_increasing
import Theorems.Thm_thm_2_5_gap_measurable
import Theorems.Thm_thm_2_5_gap_measure
import Theorems.Thm_thm_2_4
import Theorems.Thm_thm_2_5_gap_iUnion_eq
import Definitions.Def_ProbabilityTheory_chapter_02_thm_2_5_F000
import Definitions.Def_ProbabilityTheory_chapter_02_def_2_6_F000
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Tactic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set

theorem solution {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (A : ℕ → Set Ω) (hA : SetSeqDecreasing A)
    (hMeas : ∀ i, MeasurableSet (A i)) (hfin : μ (A 0) < ⊤) :
    μ (⋂ i, A i) = ⨅ i, μ (A i) := by
  have hA0_ne_top : μ (A 0) ≠ ⊤ := ne_top_of_lt hfin
  have hInter_subset : (⋂ i, A i) ⊆ A 0 := iInter_subset A 0
  have hInter_fin : μ (⋂ i, A i) ≤ μ (A 0) := measure_mono hInter_subset
  have hsource :
      μ (⋃ i, thm_2_5_gap A i) = ⨆ i, μ (thm_2_5_gap A i) :=
    thm_2_4 μ (thm_2_5_gap A) (thm_2_5_gap_increasing hA)
      (thm_2_5_gap_measurable hMeas)
  rw [← ENNReal.sub_sub_cancel hA0_ne_top (iInf_le (fun i => μ (A i)) 0),
    ENNReal.sub_iInf, ← ENNReal.sub_sub_cancel hA0_ne_top hInter_fin,
    ← measure_sdiff hInter_subset (.iInter fun i => (hMeas i).nullMeasurableSet)
      (ne_top_of_le_ne_top hA0_ne_top hInter_fin),
    ← thm_2_5_gap_iUnion_eq A, hsource]
  exact congrArg (fun t => μ (A 0) - t)
    (iSup_congr fun i => thm_2_5_gap_measure μ hA hMeas hfin i)
