-- Prove2me | solution 1 for lambdaSystem_iff_exists_dynkinSystem
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T21:15:17.672975+00:00
-- url     : https://prove2.me/submissions/d1ad1d7f-fa95-421c-aef5-68458177729a

import Definitions.Def_ProbabilityTheory_chapter_03_def_3_10_F000
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Pairwise.Basic
import Mathlib.MeasureTheory.PiSystem


/-

 # Definition 3.10  Lambda system and Pi system

-/

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set

variable {Ω : Type*}


theorem solution {L : Set (Set Ω)} :
    LambdaSystem L ↔
      ∃ d : MeasurableSpace.DynkinSystem Ω, ∀ A : Set Ω, d.Has A ↔ A ∈ L := by
  constructor
  · intro h
    refine ⟨{
      Has := fun A ↦ A ∈ L
      has_empty := by simpa using h.compl_mem h.univ_mem
      has_compl := h.compl_mem
      has_iUnion_nat := h.iUnion_mem
    }, fun _ ↦ Iff.rfl⟩
  · rintro ⟨d, hd⟩
    constructor
    · exact (hd _).mp d.has_univ
    · intro A hA
      exact (hd _).mp (d.has_compl ((hd _).mpr hA))
    · intro f hf hL
      apply (hd _).mp
      exact d.has_iUnion_nat (fun i j hij ↦ by simpa using hf hij) (fun i ↦ (hd _).mpr (hL i))