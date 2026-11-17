-- Prove2me | solution 1 for thm_2_1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T21:41:39.594127+00:00
-- url     : https://prove2.me/submissions/68b5ddc0-53c2-4787-8b01-2bfeb1e7e268

import Theorems.Thm_thm_2_1_part1
import Theorems.Thm_thm_2_1_part2
import Definitions.Def_ProbabilityTheory_chapter_02_def_2_4_F000
import Mathlib.Tactic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set

theorem solution {Ω : Type*} (E : ℕ → Set Ω) :
    (∀ ω, ω ∈ setLiminf E ↔ ∃ N : ℕ, ∀ n ≥ N, ω ∈ E n) ∧
      (∀ ω, ω ∈ setLimsup E ↔ ∀ N : ℕ, ∃ n ≥ N, ω ∈ E n) := by
  exact ⟨thm_2_1_part1 E, thm_2_1_part2 E⟩
