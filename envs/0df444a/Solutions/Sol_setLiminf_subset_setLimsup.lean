-- Prove2me | solution 1 for setLiminf_subset_setLimsup
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T21:07:43.384201+00:00
-- url     : https://prove2.me/submissions/5bef2c88-2a9d-46e7-8cee-9a5165c08fd7

import Definitions.Def_ProbabilityTheory_chapter_02_def_2_4_F000
import Mathlib.Tactic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set

theorem solution {Ω : Type*} (E : ℕ → Set Ω) :
    setLiminf E ⊆ setLimsup E := by
  intro x hx
  rcases mem_iUnion.mp hx with ⟨j, hj⟩
  rw [setLimsup, mem_iInter]
  intro n
  rw [mem_iUnion]
  refine ⟨max n j, ?_⟩
  rw [mem_iUnion]
  refine ⟨le_max_left n j, ?_⟩
  exact mem_iInter₂.mp hj (max n j) (le_max_right n j)
