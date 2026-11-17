-- Prove2me | solution 1 for measurable_seqInfEReal
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T21:12:53.865871+00:00
-- url     : https://prove2.me/submissions/d2cfa7e7-f0cd-42d6-a5f5-7dd68ebcfd26

import Theorems.Thm_measurable_seqSupEReal
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
  : Measurable (fun ω => seqInf (fun i => f i ω)) := by
  simpa [seqInf] using (Measurable.iInf hf)
