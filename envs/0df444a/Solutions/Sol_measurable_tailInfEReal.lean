-- Prove2me | solution 1 for measurable_tailInfEReal
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T21:13:08.649643+00:00
-- url     : https://prove2.me/submissions/b64a837f-59b2-47ee-97ba-3e677ec79d71

import Theorems.Thm_measurable_tailSupEReal
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
    (hf : ∀ i, Measurable (f i)) (n : ℕ) :
    Measurable (fun ω => tailInf (fun i => f i ω) n) := by
  simpa [tailInf] using (Measurable.iInf fun k => hf (n + k))
