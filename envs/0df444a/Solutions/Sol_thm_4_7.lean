-- Prove2me | solution 1 for thm_4_7
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T21:20:47.85221+00:00
-- url     : https://prove2.me/submissions/8393c796-68e4-4ea1-8b94-7668b56a5dd7

import Theorems.Thm_measurable_seqSupEReal
import Theorems.Thm_measurable_seqInfEReal
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
    (hf : ∀ i, Measurable (f i)) :
    Measurable (fun ω => seqSup (fun i => f i ω)) ∧
      Measurable (fun ω => seqInf (fun i => f i ω)) := by
  exact ⟨measurable_seqSupEReal f hf, measurable_seqInfEReal f hf⟩
