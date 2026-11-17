-- Prove2me | solution 1 for def_2_4_eq_setLimsup
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T21:18:30.904295+00:00
-- url     : https://prove2.me/submissions/09e98b07-a65f-4471-9e2d-190781cc70af

import Definitions.Def_ProbabilityTheory_chapter_02_def_2_4_F000
import Theorems.Thm_setLiminf_subset_setLimsup
import Theorems.Thm_def_2_4_eq_setLiminf
import Mathlib.Tactic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set

theorem solution {Ω : Type*} (E : ℕ → Set Ω)
    (h : setSeqLimitExists E) :
    def_2_4 E h = setLimsup E := by
  exact h
