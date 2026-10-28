-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_upper_endpoint_two_sided_exit_expectation_one
-- name    : AvramDividend.Classical.chat04_upper_endpoint_two_sided_exit_expectation_one
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T09:35:33.572082+00:00
-- url     : https://prove2.me/theorems/4f871287-bf29-4860-8d54-596d7d7b830b
-- title:
--   Two-sided upward-before-ruin q-discounted expectation equals one at the upper initial-reserve endpoint
-- statement:
--   If upward first passage above zero is instantaneous almost surely and first passage below the lower level −a occurs strictly after time zero almost surely, then starting at the upper reserve boundary x=a, the strict upper-before-downward event occurs immediately with discount one. Its exact Prove2Me discounted two-sided exit expectation equals one. This is a full probability-level upper-endpoint result independent of q-scale harmonicity.
-- source:
--   Uses the canonical twoSidedExitExpectation and the probability-measure field of SpectrallyNegativeLevy, together with the strict up/down clock conditions. The first condition is supplied by upcoming chat04_up_exit_time_zero_of_positive_near_zero (35cd74d9-4a9b-49ea-987c-66fa22b9902f). Direct upper-endpoint specialisation of alternative Open two_sided_exit_before_ruin_identity (5bcf90e1-211c-42db-beac-d92aeb95b5c9), parent 3e1ce2c8. Only path regularity assumptions remain.

import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Analysis.Complex.Exponential
import Definitions.Def_AvramDividend_Classical_TwoSidedExit

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat04_upper_endpoint_two_sided_exit_expectation_one
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q a : ℝ)
    (hup0 : ∀ᵐ ω ∂P, twoSidedExitUpTime X 0 ω = 0)
    (hdownpos : ∀ᵐ ω ∂P,
      0 < twoSidedExitDownTime X (-a) ω) :
    twoSidedExitExpectation X q a a = 1 := by sorry
