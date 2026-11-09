-- Prove2me | solution 1 for levy_foundations_arrivalSurvivalPolynomialNonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-08T00:31:35.964799+00:00
-- url     : https://prove2.me/submissions/68cbcf31-6ab8-44e6-b589-d5370e5ae9d4

import Mathlib.Probability.Distributions.Gamma
import Definitions.Def_levy_foundations_arrivalSurvivalPolynomial

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

theorem solution {R t : ℝ} (hR : 0 ≤ R) (ht : 0 ≤ t) (n : ℕ) :
    0 ≤ LevyFoundations.arrivalSurvivalPolynomial R n t := by
  unfold LevyFoundations.arrivalSurvivalPolynomial
  exact mul_nonneg (Real.exp_pos _).le (Finset.sum_nonneg fun _ _ =>
    div_nonneg (pow_nonneg (mul_nonneg hR ht) _) (Nat.cast_nonneg _))
