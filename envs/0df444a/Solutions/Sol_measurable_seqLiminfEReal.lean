-- Prove2me | solution 1 for measurable_seqLiminfEReal
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T21:23:45.901549+00:00
-- url     : https://prove2.me/submissions/4d929453-307b-4b4a-93fd-d67cb1e6fb6c

import Theorems.Thm_measurable_tailSupEReal
import Theorems.Thm_measurable_tailInfEReal
import Theorems.Thm_measurable_seqLimsupEReal
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
    (hf : ∀ i, Measurable (f i)) : Measurable (fun ω => seqLiminf (fun i => f i ω)) := by
  simpa [seqLiminf] using (Measurable.iSup fun n => measurable_tailInfEReal f hf n)
