-- Prove2me | Theorems.Thm_AvramDividend_Classical_identically_law_fixed_marks_expectation_ws01b
-- name    : AvramDividend.Classical.identically_law_fixed_marks_expectation_ws01b
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T16:01:33.842302+00:00
-- url     : https://prove2.me/theorems/b9c39f0d-f795-4b78-aad0-4171ec095c8c
-- title:
--   Bochner expectation of a finite sequence of identically distributed integrable marks
-- statement:
--   For an actual probability space and arbitrary measurable mark random variables sharing the same law ν, the expectation of their first j test-function values equals j times the ν-expectation. No mark independence is needed, only common distribution and integrability. This supports finite Poisson count-cell compensation without inaccessible private process definitions.
-- source:
--   Generalised from LeanLevy/RandomMeasure/PoissonPointFamily.lean (MIT, 2026 LeanLevy contributors), to a standalone public HasLaw formula with only pinned Mathlib dependencies.

import Mathlib

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

theorem AvramDividend.Classical.identically_law_fixed_marks_expectation_ws01b
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ν : Measure E)
    (Y : ℕ → Ω → E)
    (hYm : ∀ n, Measurable (Y n))
    (hYL : ∀ n, HasLaw (Y n) ν μ)
    (j : ℕ) (f : E → ℝ) (hf : Measurable f)
    (hfI : Integrable f ν) :
    (∫ ω, ∑ n ∈ Finset.range j, f (Y n ω) ∂μ) =
      (j : ℝ) * ∫ y, f y ∂ν := by sorry
