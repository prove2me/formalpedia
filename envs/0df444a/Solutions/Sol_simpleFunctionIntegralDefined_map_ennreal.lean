-- Prove2me | solution 1 for simpleFunctionIntegralDefined_map_ennreal
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T21:59:43.158524+00:00
-- url     : https://prove2.me/submissions/28b9e31d-8fc1-4851-b8d6-ea47039097b5

import Theorems.Thm_not_simpleFunctionHasNegInf_map_ennreal
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

theorem solution
    (μ : Measure Ω) (X : SimpleFunc Ω ENNReal) :
    simpleFunctionIntegralDefined μ (X.map fun x : ENNReal => (x : EReal)) := by
  -- By definition of `simpleFunctionIntegralDefined`, we need to show that if `X.map (fun x => x : ENNReal → EReal)` has a positive infinite term, it cannot have a negative infinite term.
  unfold simpleFunctionIntegralDefined
  intro h_contra
  obtain ⟨x, hx⟩ := h_contra;
  convert not_simpleFunctionHasNegInf_map_ennreal μ X hx using 1
