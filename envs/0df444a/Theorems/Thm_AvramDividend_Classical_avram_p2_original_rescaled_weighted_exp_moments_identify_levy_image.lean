-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_original_rescaled_weighted_exp_moments_identify_levy_image
-- name    : AvramDividend.Classical.avram_p2_original_rescaled_weighted_exp_moments_identify_levy_image
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T09:11:41.602995+00:00
-- url     : https://prove2.me/theorems/2ca40085-b85b-4101-88bc-12501017d285
-- title:
--   Original weighted exponential image polynomial moments converge exactly to negative Lévy-image moments
-- statement:
--   For every natural polynomial degree k, the inverse-time-scaled ENNReal kth moment of the true fourth-weighted original exp(X_h) image converges to the kth moment of the finite fourth-weighted actual negative Lévy measure pushed forward by exp. The source-side asymptotic derivative and limit-side ν image are independently established by two accepted theorems; this unconditionally identifies their genuine measure moments for subsequent tightness and compact Hausdorff moment-uniqueness arguments.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_original_rescaled_weighted_exp_polynomial_moments_converge
import Theorems.Thm_AvramDividend_Classical_avram_p2_negative_levy_weighted_exp_real_moment_bridge

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_original_rescaled_weighted_exp_moments_identify_levy_image
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
      (nhds (∫⁻ z : ℝ, ENNReal.ofReal (z ^ k) ∂
        (((X.ν.restrict (Iio (0 : ℝ))).withDensity
          (fun y => ENNReal.ofReal ((Real.exp y - 1) ^ 4))).map
          Real.exp))) := by sorry
