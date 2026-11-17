-- Prove2me | solution 1 for textbookIntegrable_implies_some
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T21:52:38.372308+00:00
-- url     : https://prove2.me/submissions/1d90f5e7-ee9c-4987-911b-1ad9616b3908

import Theorems.Thm_textbookIntegrable_pos_ne_top
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
    ∃ v : EReal, textbookIntegral μ X = some v := by
  unfold textbookIntegral
  have hUndefined :
      ¬ (Def65Support.posLIntegral μ X = ⊤ ∧ Def65Support.negLIntegral μ X = ⊤) := by
    intro hBothTop
    exact (textbookIntegrable_pos_ne_top hX) hBothTop.1
  refine ⟨(Def65Support.posLIntegral μ X : EReal) - (Def65Support.negLIntegral μ X : EReal), ?_⟩
  simp [hUndefined]
end TextbookIntegralLemmas
