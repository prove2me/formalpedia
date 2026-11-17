-- Prove2me | solution 1 for simpleFunctionIntegralFinChain_succ
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T23:29:44.634024+00:00
-- url     : https://prove2.me/submissions/a38290be-b7e7-463b-af7a-afe46433a034

import Definitions.Def_ProbabilityTheory_chapter_06_def_6_2_F001
import Definitions.Def_ProbabilityTheory_chapter_06_def_6_2_F000
import Mathlib.MeasureTheory.Function.SimpleFunc
import Mathlib.Tactic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped BigOperators
variable {Ω : Type*} [MeasurableSpace Ω]

theorem solution (μ : Measure Ω) (n : ℕ)
    (F : Fin (n + 1) → SimpleFunc Ω EReal) :
    simpleFunctionIntegralFinChain μ (n + 1) F =
      match simpleFunctionIntegralFinChain μ n (fun i => F i.succ) with
      | some _ => simpleFunctionIntegralAdd μ (F 0) (∑ i : Fin n, F i.succ)
      | none => none := by
  rfl
