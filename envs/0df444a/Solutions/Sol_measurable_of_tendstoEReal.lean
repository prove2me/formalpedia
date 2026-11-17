-- Prove2me | solution 1 for measurable_of_tendstoEReal
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T21:52:58.742686+00:00
-- url     : https://prove2.me/submissions/d57b9494-56a7-4396-9469-c694bacfa819

import Theorems.Thm_measurable_seqLimsupEReal
import Theorems.Thm_seqLimsup_eq_filter_limsupEReal
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
    Measurable g := by
  have h_eq : g = fun ω => seqLimsup (fun i => f i ω) := by
    funext ω
    have h_limsup :
        Filter.limsup (fun n => f n ω) Filter.atTop ≤ g ω := by
      rw [Filter.limsup_le_iff]
      intro y hy
      exact (hg ω) (Iio_mem_nhds hy)
    have h_liminf :
        g ω ≤ Filter.liminf (fun n => f n ω) Filter.atTop := by
      rw [Filter.le_liminf_iff]
      intro y hy
      exact (hg ω) (Ioi_mem_nhds hy)
    have h_ge_limsup :
        g ω ≤ Filter.limsup (fun n => f n ω) Filter.atTop := by
      exact le_trans h_liminf (Filter.liminf_le_limsup (u := fun n => f n ω) (f := Filter.atTop))
    calc
      g ω = Filter.limsup (fun n => f n ω) Filter.atTop := le_antisymm h_ge_limsup h_limsup
      _ = seqLimsup (fun n => f n ω) := (seqLimsup_eq_filter_limsupEReal (fun n => f n ω)).symm
  rw [h_eq]
  exact measurable_seqLimsupEReal f hf
