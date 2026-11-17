-- Prove2me | solution 1 for thm_4_8
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T21:59:51.497207+00:00
-- url     : https://prove2.me/submissions/bc1da47b-5046-4865-9160-bc91d680834e

import Theorems.Thm_measurable_seqLimsupEReal
import Theorems.Thm_measurable_seqLiminfEReal
import Theorems.Thm_measurable_of_tendstoEReal
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
    (hf : ∀ i, Measurable (f i)) {g : Ω → EReal}
    (hg : ∀ ω, Filter.Tendsto (fun n => f n ω) Filter.atTop (𝓝 (g ω))) :
    Measurable (fun ω => seqLimsup (fun i => f i ω)) ∧
      Measurable (fun ω => seqLiminf (fun i => f i ω)) ∧
      Measurable g := by
  exact ⟨measurable_seqLimsupEReal f hf, measurable_seqLiminfEReal f hf,
    measurable_of_tendstoEReal f hf hg⟩
