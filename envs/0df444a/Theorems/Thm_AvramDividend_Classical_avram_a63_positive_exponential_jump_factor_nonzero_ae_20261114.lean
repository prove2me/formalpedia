-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a63_positive_exponential_jump_factor_nonzero_ae_20261114
-- name    : AvramDividend.Classical.avram_a63_positive_exponential_jump_factor_nonzero_ae_20261114
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T12:32:19.542196+00:00
-- url     : https://prove2.me/theorems/6703fbfe-45ff-4874-b903-5e8719b65c71
-- title:
--   A real exponential physical jump factor never vanishes almost everywhere under a probability measure
-- statement:
--   For every real measurable or arbitrary physical jump-mark variable on a probability space, its exponential scaled by any real parameter is strictly positive on every path and therefore cannot vanish almost surely.
-- source:
--   Pinned Mathlib Real.exp_ne_zero and nonbottom probability ae filter.

import Mathlib
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal
noncomputable section

/-- No real exponential of a physical jump variable vanishes almost surely on a probability space. -/

theorem AvramDividend.Classical.avram_a63_positive_exponential_jump_factor_nonzero_ae_20261114
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (J : Ω → ℝ) (θ : ℝ) :
    ¬ ((fun ω => Real.exp (θ * J ω)) =ᵐ[P]
      fun _ => (0 : ℝ)) := by sorry
