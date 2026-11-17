-- Prove2me | solution 1 for measurable_seqSupEReal
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T21:07:05.143223+00:00
-- url     : https://prove2.me/submissions/7524ea17-9763-4ee1-a6c6-a4fdfc9062c5

import Definitions.Def_ProbabilityTheory_chapter_04_def_4_3_sup_inf_F000
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Tactic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory

theorem solution {Ω : Type*} [MeasurableSpace Ω] (f : ℕ → Ω → EReal)
    (hf : ∀ i, Measurable (f i))
  : Measurable (fun ω => seqSup (fun i => f i ω)) := by
  simpa [seqSup] using (Measurable.iSup hf)
