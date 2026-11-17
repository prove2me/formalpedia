-- Prove2me | solution 1 for piSystem_iff_isPiSystem
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T21:14:59.559935+00:00
-- url     : https://prove2.me/submissions/cbadc7c2-ed68-41a6-915d-ee9bdb4494f4

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


theorem solution {Ω : Type*} {P : Set (Set Ω)} (empty_mem : ∅ ∈ P) :
    PiSystem P ↔ IsPiSystem P := by
  constructor
  · intro h A hA B hB _
    exact h.2 hA hB
  · intro h
    constructor
    · exact ⟨∅, empty_mem⟩
    · intro A hA B hB
      by_cases hAB : (A ∩ B).Nonempty
      · exact h A hA B hB hAB
      · rw [Set.not_nonempty_iff_eq_empty.mp hAB]
        exact empty_mem