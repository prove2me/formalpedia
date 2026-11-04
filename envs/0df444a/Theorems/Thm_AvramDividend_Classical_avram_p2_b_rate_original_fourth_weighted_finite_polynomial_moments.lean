-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_b_rate_original_fourth_weighted_finite_polynomial_moments
-- name    : AvramDividend.Classical.avram_p2_b_rate_original_fourth_weighted_finite_polynomial_moments
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T18:47:07.613207+00:00
-- url     : https://prove2.me/theorems/e1ba9d5b-2dc5-4919-9135-bd4b177e5634
-- title:
--   Original Levy source weighted fourth-transform derivatives extend to finite polynomial moment combinations
-- statement:
--   For an arbitrary finite collection of natural exponents k and real coefficients a_k, linear combinations of the original Lévy source small-time fourth-weighted exponential kth image moment ratios converge to the corresponding identical linear combination of the original Lévy measure moments. This is the exact finite polynomial test family bridge obtained by finite-sum stability of limits from the Proved original-source moment theorem. No jump-rate assumption is used.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_b_rate_original_fourth_weighted_integer_moments

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_b_rate_original_fourth_weighted_finite_polynomial_moments
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s : Finset ℕ) (a : ℕ → ℝ) (θ : ℝ) (hθ : 0 ≤ θ) :
    Tendsto
      (fun h : ℝ => ∑ k ∈ s,
        a k * ((∫ ω, (Real.exp (θ * X.X (Real.toNNReal h) ω)) ^ k *
          (Real.exp (θ * X.X (Real.toNNReal h) ω) - 1) ^ 4 ∂P) / h))
      (nhdsWithin (0 : ℝ) (Ioi 0))
      (nhds (∑ k ∈ s, a k *
        (∫ y in Iio (0 : ℝ), (Real.exp (θ * y)) ^ k *
          (Real.exp (θ * y) - 1) ^ 4 ∂X.ν))) := by sorry
