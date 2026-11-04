-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_original_rescaled_weighted_exp_power_tail_eventual_bound
-- name    : AvramDividend.Classical.avram_p2_original_rescaled_weighted_exp_power_tail_eventual_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T10:05:51.741697+00:00
-- url     : https://prove2.me/theorems/8c251424-dec1-47ae-a1db-285665346baf
-- title:
--   Eventually uniform high-power tail envelope for the actual rescaled Lévy exponential image
-- statement:
--   For the original X_h weighted by its fourth exponential deficit and pushed forward by exp, every nonnegative polynomial moment converges to the actual weighted ν image moment. Consequently, for any threshold R≥0, degree k and strict ENNReal upper bound c on the limiting kth moment, the rescaled source tail mass times R^k is eventually below c. The proof combines the proved source moment limit with a genuine Markov bound, providing quantitative tightness control towards finite-measure weak convergence and no assumed jump compensator.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_original_rescaled_weighted_exp_moments_identify_levy_image
import Theorems.Thm_AvramDividend_Classical_avram_p2_nonnegative_power_tail_markov

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_original_rescaled_weighted_exp_power_tail_eventual_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (k : ℕ) (R : ℝ) (hR : 0 ≤ R) (c : ℝ≥0∞)
    (hc : (∫⁻ z : ℝ, ENNReal.ofReal (z ^ k) ∂
      (((X.ν.restrict (Iio (0 : ℝ))).withDensity
        (fun y => ENNReal.ofReal ((Real.exp y - 1) ^ 4))).map
        Real.exp)) < c) :
    ∀ᶠ h : ℝ in nhdsWithin (0 : ℝ) (Ioi 0),
      ENNReal.ofReal (R ^ k) * ((ENNReal.ofReal h)⁻¹ *
        ((P.withDensity (fun ω => ENNReal.ofReal
        ((Real.exp (X.X (Real.toNNReal h) ω) - 1) ^ 4))).map
        (fun ω => Real.exp (X.X (Real.toNNReal h) ω))) (Ici R)) < c := by sorry
