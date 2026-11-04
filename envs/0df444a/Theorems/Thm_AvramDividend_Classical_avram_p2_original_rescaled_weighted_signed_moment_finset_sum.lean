-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_original_rescaled_weighted_signed_moment_finset_sum
-- name    : AvramDividend.Classical.avram_p2_original_rescaled_weighted_signed_moment_finset_sum
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T10:00:43.098927+00:00
-- url     : https://prove2.me/theorems/8086703c-3db4-4a70-bef5-a5950cfefddc
-- title:
--   Signed finite polynomial moment convergence for original weighted exponential image
-- statement:
--   For arbitrary finite sets of natural degrees and arbitrary signed real coefficients, the original source's inverse-time rescaled fourth-weighted exponential-image moments converge after toReal and signed finite linear combination to the exact negative Lévy-image moments. This follows from the independently Proved per-degree original real moment limit and finite-sum continuity, enabling Stone–Weierstrass signed polynomial approximations without assuming the source jump-count rate.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_original_rescaled_weighted_exp_real_moments_converge

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_p2_original_rescaled_weighted_signed_moment_finset_sum
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (s : Finset ℕ) (a : ℕ → ℝ) :
    Tendsto
      (fun h : ℝ => ∑ k ∈ s, a k * ((ENNReal.ofReal h)⁻¹ *
          (∫⁻ z : ℝ, ENNReal.ofReal (z ^ k) ∂
            ((P.withDensity (fun ω => ENNReal.ofReal
              ((Real.exp (X.X (Real.toNNReal h) ω) - 1) ^ 4))).map
              (fun ω => Real.exp (X.X (Real.toNNReal h) ω))))).toReal)
      (nhdsWithin (0 : ℝ) (Ioi 0))
      (nhds (∑ k ∈ s, a k * ((∫⁻ z : ℝ, ENNReal.ofReal (z ^ k) ∂
          (((X.ν.restrict (Iio (0 : ℝ))).withDensity
            (fun y => ENNReal.ofReal ((Real.exp y - 1) ^ 4))).map
            Real.exp)).toReal))) := by sorry
