-- Prove2me | solution 1 for measurable_seqLimsupEReal
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T21:18:38.790454+00:00
-- url     : https://prove2.me/submissions/d65e705e-8547-420a-ada1-646de779c928

import Theorems.Thm_measurable_tailSupEReal
import Theorems.Thm_measurable_tailInfEReal
import Definitions.Def_ProbabilityTheory_chapter_04_def_4_3_limsup_liminf_F000
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Tactic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped Topology

theorem solution {Ω : Type*} [MeasurableSpace Ω] (f : ℕ → Ω → EReal)
    (hf : ∀ i, Measurable (f i)) : Measurable (fun ω => seqLimsup (fun i => f i ω)) := by
  simpa [seqLimsup] using (Measurable.iInf fun n => measurable_tailSupEReal f hf n)
