-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja18p1a2_uniform_small_exp_remainder_rate
-- name    : AvramDividend.Classical.avram_ja18p1a2_uniform_small_exp_remainder_rate
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T01:55:40.507699+00:00
-- url     : https://prove2.me/theorems/2efe3c4d-02de-4f02-8fab-f10c3406f920
-- title:
--   Uniform original small-negative compensated exponential rate
-- statement:
--   Uniformly over theta in (0,1], the original small-negative compensated exponent integral divided by theta is bounded above by a finite constant. Follows from compensated_exponential_quadratic_of_small_argument and finite_small_negative_jump_square_moment, with no large-negative first moment.
-- source:
--   Necessary child of J-A18 P1A b0d050e0.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_ja18p1a2_uniform_small_exp_remainder_rate
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) :
    ∃ K : ℝ, ∀ θ : ℝ, 0 < θ → θ ≤ 1 →
      (∫ z in Ioo (-1 : ℝ) 0,
        (Real.exp (θ * z) - 1 - θ * z) ∂X.ν) / θ ≤ K := by sorry
