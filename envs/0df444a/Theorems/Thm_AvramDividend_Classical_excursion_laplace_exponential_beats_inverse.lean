-- Prove2me | Theorems.Thm_AvramDividend_Classical_excursion_laplace_exponential_beats_inverse
-- name    : AvramDividend.Classical.excursion_laplace_exponential_beats_inverse
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T07:13:40.415425+00:00
-- url     : https://prove2.me/theorems/83dd767a-3fa0-499b-bb9d-793f9a9323cb
-- title:
--   Exponential Laplace decay beats any inverse-linear lower bound at positive heights
-- statement:
--   For every positive level x and positive tolerance r, some Laplace parameter θ>0 satisfies θe^(−θx)<r. This formalises the exponential-versus-inverse-linear separation used to prove that a killed-subordinator potential with a reciprocal-linear lower Laplace bound must charge every interval (0,x]. It follows from the pinned Mathlib theorem t e^(−t)→0 as t→+∞.
-- source:
--   Pinned Mathlib Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero; positive support of Esscher tilted ladder potential.

import Mathlib
open Filter Topology

theorem AvramDividend.Classical.excursion_laplace_exponential_beats_inverse
    (r x : ℝ) (hr : 0 < r) (hx : 0 < x) :
    ∃ θ : ℝ, 0 < θ ∧ θ * Real.exp (-(θ * x)) < r := by sorry
