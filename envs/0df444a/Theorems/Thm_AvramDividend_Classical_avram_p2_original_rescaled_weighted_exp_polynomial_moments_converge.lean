-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_original_rescaled_weighted_exp_polynomial_moments_converge
-- name    : AvramDividend.Classical.avram_p2_original_rescaled_weighted_exp_polynomial_moments_converge
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T09:01:14.888015+00:00
-- url     : https://prove2.me/theorems/80b36d47-5082-40db-9391-038fab95e38a
-- title:
--   All original rescaled weighted exponential polynomial moments converge to actual Lévy moments
-- statement:
--   For the original spectrally negative Lévy process on its given probability space, every inverse-time rescaled polynomial ENNReal moment of the true fourth-weighted exp(X_h) image converges as h tends to zero from above to the ENNReal of the corresponding genuine ν-integral on negative marks. This turns the independently proved real fourth-weighted exponential derivative and real-to-lintegral moment bridge into finite-measure moment convergence, a core analytic premise for tightness and weak uniqueness; no jump compensator or count identity is assumed.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_original_weighted_exp_real_moment_bridge
import Theorems.Thm_AvramDividend_Classical_avram_wave6_01_original_source_fourth_weighted_exponential_small_time_derivative

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_original_rescaled_weighted_exp_polynomial_moments_converge
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (k : ℕ) :
    Tendsto
      (fun h : ℝ => (ENNReal.ofReal h)⁻¹ *
        (∫⁻ z : ℝ, ENNReal.ofReal (z ^ k) ∂
          ((P.withDensity (fun ω => ENNReal.ofReal
            ((Real.exp (X.X (Real.toNNReal h) ω) - 1) ^ 4))).map
            (fun ω => Real.exp (X.X (Real.toNNReal h) ω)))))
      (nhdsWithin (0 : ℝ) (Ioi 0))
      (nhds (ENNReal.ofReal
        (∫ y in Iio (0 : ℝ), Real.exp ((k : ℝ) * y) *
          (Real.exp y - 1) ^ 4 ∂X.ν))) := by sorry
