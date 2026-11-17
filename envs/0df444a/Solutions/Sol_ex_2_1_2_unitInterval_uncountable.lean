-- Prove2me | solution 1 for ex_2_1_2_unitInterval_uncountable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T21:21:27.657506+00:00
-- url     : https://prove2.me/submissions/af1d50e5-0569-4249-a985-7b8b1b1415c5

import Definitions.Def_ProbabilityTheory_chapter_02_def_2_1_F000
import Definitions.Def_ProbabilityTheory_chapter_02_ex_2_1_2_F000
import Mathlib.Analysis.Real.Cardinality
import Mathlib.Tactic
import Theorems.Thm_ex_2_1_2_binary_sequences_no_nat_injection

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped Set
open scoped BigOperators

noncomputable section

theorem solution :
    ¬ IsCountableSet (Set.Icc (0 : ℝ) 1) := by
  rintro ⟨e⟩
  exact ex_2_1_2_binary_sequences_no_nat_injection ⟨
    fun s => (e (cantorIntervalEmbedding s)).1,
    by
      intro s t hst
      apply cantorIntervalEmbedding_injective
      apply e.injective
      ext
      exact hst⟩
