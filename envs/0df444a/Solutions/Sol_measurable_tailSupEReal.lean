-- Prove2me | solution 1 for measurable_tailSupEReal
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T21:07:21.376951+00:00
-- url     : https://prove2.me/submissions/382c5d52-6ced-467c-9468-9611497016b0

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
    Measurable (fun ω => tailSup (fun i => f i ω) n) := by
  simpa [tailSup] using (Measurable.iSup fun k => hf (n + k))
