-- Prove2me | solution 1 for thm_2_4_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T21:13:40.490621+00:00
-- url     : https://prove2.me/submissions/de1987a9-1af7-48c5-b942-e08c15839a4d

import Definitions.Def_ProbabilityTheory_chapter_02_def_2_6_F000
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Tactic
import Theorems.Thm_thm_2_4

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped BigOperators

theorem solution {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (A : ℕ → Set Ω) (hA : SetSeqIncreasing A) (hAmeas : ∀ n, MeasurableSet (A n)) :
    Filter.Tendsto (fun i => μ (A i)) Filter.atTop (nhds (μ (⋃ i, A i))) := by
  have hmono : Monotone fun i => μ (A i) := fun i j hij => measure_mono (hA hij)
  have hsup : μ (⋃ i, A i) = ⨆ i, μ (A i) := thm_2_4 μ A hA hAmeas
  rw [hsup]
  exact tendsto_atTop_iSup hmono
