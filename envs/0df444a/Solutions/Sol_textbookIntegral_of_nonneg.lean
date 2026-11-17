-- Prove2me | solution 1 for textbookIntegral_of_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T21:39:48.719969+00:00
-- url     : https://prove2.me/submissions/236f1455-de5f-4a53-b1f3-1775b89d1a13

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

theorem solution
    (_hX : ∀ ω, 0 ≤ X ω)
    (hneg_zero :
      Def65Support.negLIntegral μ X = 0) :
    textbookIntegral μ X = some (Def65Support.posLIntegral μ X : EReal) := by
  unfold textbookIntegral
  have hUndefined :
      ¬ (Def65Support.posLIntegral μ X = ⊤ ∧ Def65Support.negLIntegral μ X = ⊤) := by
    intro hBothTop
    simpa [hneg_zero] using hBothTop.2
  simp [hneg_zero]
end TextbookIntegralLemmas
