-- Prove2me | solution 1 for thm_2_1_part1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T21:29:46.709531+00:00
-- url     : https://prove2.me/submissions/498ae2ec-d27e-41ff-9376-f1d9ec6e1c0b

import Definitions.Def_ProbabilityTheory_chapter_02_def_2_4_F000
import Theorems.Thm_setLiminf_subset_setLimsup
import Theorems.Thm_def_2_4_eq_setLiminf
import Theorems.Thm_def_2_4_eq_setLimsup
import Mathlib.Tactic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set

theorem solution {Ω : Type*} (E : ℕ → Set Ω) :
   (∀ ω, ω ∈ setLiminf E ↔ ∃ N : ℕ, ∀ n ≥ N, ω ∈ E n) := by
  intro ω
  constructor
  · intro hω
    rcases mem_iUnion.mp hω with ⟨N, hN⟩
    refine ⟨N, ?_⟩
    intro n hn
    exact mem_iInter₂.mp hN n hn
  · rintro ⟨N, hN⟩
    refine mem_iUnion.mpr ⟨N, ?_⟩
    exact mem_iInter₂.mpr hN
