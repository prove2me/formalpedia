-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_original_rescaled_weighted_exp_real_moments_converge
-- name    : AvramDividend.Classical.avram_p2_original_rescaled_weighted_exp_real_moments_converge
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T09:51:49.550197+00:00
-- url     : https://prove2.me/theorems/78c1dde2-e111-48c3-963f-772128313547
-- title:
--   Original rescaled weighted exponential image real moments converge to actual Lévy moments
-- statement:
--   For every natural k, taking toReal of the original source rescaled fourth-weighted exp(X_h) ENNReal kth moment converges to toReal of the finite actual negative Lévy-image kth moment. The exact source ENNReal convergence and finite ν-integral have previously been Proved. This is the analytic bridge needed for signed finite-polynomial test functions and subsequent continuous-function approximation; no jump-count identity or compensator is assumed.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_original_rescaled_weighted_exp_moments_identify_levy_image
import Theorems.Thm_AvramDividend_Classical_avram_p2_negative_levy_weighted_exp_real_moment_bridge

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_original_rescaled_weighted_exp_real_moments_converge
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (k : ℕ) :
    Tendsto
      (fun h : ℝ => ((ENNReal.ofReal h)⁻¹ * (∫⁻ z : ℝ, ENNReal.ofReal (z ^ k) ∂
          ((P.withDensity (fun ω => ENNReal.ofReal
            ((Real.exp (X.X (Real.toNNReal h) ω) - 1) ^ 4))).map
            (fun ω => Real.exp (X.X (Real.toNNReal h) ω))))).toReal)
      (nhdsWithin (0 : ℝ) (Ioi 0))
      (nhds ((∫⁻ z : ℝ, ENNReal.ofReal (z ^ k) ∂
        (((X.ν.restrict (Iio (0 : ℝ))).withDensity
          (fun y => ENNReal.ofReal ((Real.exp y - 1) ^ 4))).map
          Real.exp)).toReal)) := by sorry
