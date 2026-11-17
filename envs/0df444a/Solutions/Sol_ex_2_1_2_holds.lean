-- Prove2me | solution 1 for ex_2_1_2_holds
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T21:41:48.42708+00:00
-- url     : https://prove2.me/submissions/02aadd0a-cc83-463a-9adc-2dfb39b478d0

import Theorems.Thm_ex_2_1_2_unitInterval_uncountable
import Definitions.Def_ProbabilityTheory_chapter_02_ex_2_1_2_F000
import Mathlib.Analysis.Real.Cardinality
import Mathlib.Tactic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped Set
open scoped BigOperators
noncomputable section

theorem solution : ex_2_1_2 := by
  exact ex_2_1_2_unitInterval_uncountable
end
