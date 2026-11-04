-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_original_rescaled_weighted_polynomial_moment_uniform
-- name    : AvramDividend.Classical.avram_p2_original_rescaled_weighted_polynomial_moment_uniform
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T09:19:26.522196+00:00
-- url     : https://prove2.me/theorems/0220add2-9d0b-4112-8bf3-61fbe2eaa6ad
-- title:
--   Every inverse-time rescaled original weighted exponential polynomial moment is uniformly finite
-- statement:
--   For any polynomial degree k, the actual P-weighted exp(X_h) kth ENNReal moment, divided by h, is bounded by an h-independent finite constant for all sufficiently small positive h. This is a direct unconditional high-moment envelope on the original process needed for uniform integrability in the finite-measure weak convergence and Hausdorff moment argument. It uses the already-Proved original high-moment O(h) estimate, with explicit inverse-time cancellation and no jump intensity hypothesis.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_original_weighted_exp_pushforward_moments_linear_smalltime_bound

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_original_rescaled_weighted_polynomial_moment_uniform
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ᶠ h : ℝ in nhdsWithin (0 : ℝ) (Ioi 0),
        (ENNReal.ofReal h)⁻¹ *
          (∫⁻ z : ℝ, ENNReal.ofReal (z ^ k) ∂
            ((P.withDensity (fun ω => ENNReal.ofReal
              ((Real.exp (X.X (Real.toNNReal h) ω) - 1) ^ 4))).map
              (fun ω => Real.exp (X.X (Real.toNNReal h) ω)))) ≤
          ENNReal.ofReal C := by sorry
