-- Prove2me | solution 1 for textbookIntegralNonnegative_eq_lintegral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T21:21:04.09431+00:00
-- url     : https://prove2.me/submissions/8bcd65bc-ca06-4012-8087-4a76468cd6ae

import Definitions.Def_ProbabilityTheory_chapter_06_def_6_3_F000
import Theorems.Thm_textbookIntegralNonnegative_eq_top_of_unbounded
import Mathlib.MeasureTheory.Function.SimpleFunc
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
variable {Ω : Type*} [MeasurableSpace Ω]

theorem solution
    (μ : Measure Ω) (X : Ω → ENNReal) :
    textbookIntegralNonnegative μ X = ∫⁻ ω, X ω ∂μ := by
  simp [
    textbookIntegralNonnegative,
    simpleApproximationSet,
    MeasureTheory.lintegral_def,
    Pi.le_def
  ]
