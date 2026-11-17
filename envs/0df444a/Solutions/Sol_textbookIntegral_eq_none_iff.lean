-- Prove2me | solution 1 for textbookIntegral_eq_none_iff
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T21:29:39.436779+00:00
-- url     : https://prove2.me/submissions/61968378-0cdd-48f1-b2ff-f9815caffb74

import Definitions.Def_ProbabilityTheory_chapter_06_def_6_5_F000
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Tactic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
namespace Def65Support
end Def65Support
section TextbookIntegralLemmas
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : Ω → EReal}

theorem solution :
    textbookIntegral μ X = none ↔
      Def65Support.posLIntegral μ X = ⊤ ∧ Def65Support.negLIntegral μ X = ⊤ := by
  unfold textbookIntegral
  by_cases hUndefined :
      Def65Support.posLIntegral μ X = ⊤ ∧ Def65Support.negLIntegral μ X = ⊤
  · simp [hUndefined]
  · simp [hUndefined]
end TextbookIntegralLemmas
