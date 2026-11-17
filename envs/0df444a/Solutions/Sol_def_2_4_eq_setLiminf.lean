-- Prove2me | solution 1 for def_2_4_eq_setLiminf
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T21:12:46.242196+00:00
-- url     : https://prove2.me/submissions/51f1712b-f1a9-4cf6-8559-43615232d960

import Definitions.Def_ProbabilityTheory_chapter_02_def_2_4_F000
import Theorems.Thm_setLiminf_subset_setLimsup
import Mathlib.Tactic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set

theorem solution {Ω : Type*} (E : ℕ → Set Ω)
    (h : setSeqLimitExists E) :
    def_2_4 E h = setLiminf E := rfl
