-- Prove2me | solution 1 for textbookIntegralNonnegative_eq_top_of_unbounded
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T21:14:37.270478+00:00
-- url     : https://prove2.me/submissions/2b4a9c0f-d79a-4bed-bd3e-6481685d5239

import Definitions.Def_ProbabilityTheory_chapter_06_def_6_3_F000
import Mathlib.MeasureTheory.Function.SimpleFunc
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
variable {Ω : Type*} [MeasurableSpace Ω]

theorem solution
    {μ : Measure Ω} {X : Ω → ENNReal}
    (h :
      ∀ C : ENNReal, C < ⊤ →
        ∃ f : SimpleFunc Ω ENNReal,
          f ∈ simpleApproximationSet X ∧ C < f.lintegral μ) :
    textbookIntegralNonnegative μ X = ⊤ := by
  by_contra htop
  have hlt : textbookIntegralNonnegative μ X < ⊤ := by
    exact (lt_top_iff_ne_top).2 htop
  rcases h (textbookIntegralNonnegative μ X) hlt with ⟨f, hfS, hf_lt⟩
  have hf_le :
      f.lintegral μ ≤ textbookIntegralNonnegative μ X := by
    exact le_iSup_of_le f (le_iSup_of_le hfS le_rfl)
  exact not_lt_of_ge hf_le hf_lt
