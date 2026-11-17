-- Prove2me | solution 1 for textbookIntegrable_neg_ne_top
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T21:34:35.537801+00:00
-- url     : https://prove2.me/submissions/84ab6431-64fd-47ad-935a-757031b3475f

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

theorem solution (hX : textbookIntegrable μ X) :
    Def65Support.negLIntegral μ X ≠ ⊤ := by
  exact ne_of_lt hX.2
end TextbookIntegralLemmas
