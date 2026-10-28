-- Prove2me | Theorems.Thm_AvramDividend_Classical_gaussian_scale_deriv_not_continuousWithinAt_zero
-- name    : AvramDividend.Classical.gaussian_scale_deriv_not_continuousWithinAt_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T13:21:47.622416+00:00
-- url     : https://prove2.me/theorems/70194706-5d98-4438-8b34-7d2e4c0c49de
-- title:
--   Ordinary Gaussian q-scale derivative is not continuous at zero from the right
-- statement:
--   For every q>0 spectrally negative Lévy scale function with Gaussian coefficient sigma>0, the ordinary two-sided real derivative function deriv W is not continuous within the nonnegative half-line at x=0. This is not a failure of Gaussian C1 smoothness at positive reserves. Proved Gaussian positive Esscher-root existence and the corrected right-derivative limit give a strictly positive right limit 2/sigma squared, while the proved ordinary-origin derivative is zero. Assuming ContinuousWithinAt (deriv W) (Ici 0) 0 would equate these distinct limits, contradiction. Explicitly invalidates hcont1 in older weighted generator-residual proof schemas, motivating the corrected right-boundary approach.
-- source:
--   Proved gaussian_scale_right_derivative_of_positive_esscher_root, positive_esscher_root_of_gaussian, and gaussian_scale_ordinary_deriv_ne_positive_right_slope, uniqueness of real limits.

import Mathlib.Topology.NhdsWithin
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_positive_esscher_root_of_gaussian
import Theorems.Thm_AvramDividend_Classical_gaussian_scale_right_derivative_of_positive_esscher_root
import Theorems.Thm_AvramDividend_Classical_gaussian_scale_ordinary_deriv_ne_positive_right_slope
open AvramDividend.Classical MeasureTheory Set Filter
open scoped Topology NNReal ENNReal

namespace AvramDividend.Classical
/-- The ordinary Gaussian scale derivative cannot be right-continuous at the origin. -/
theorem gaussian_scale_deriv_not_continuousWithinAt_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hσ : 0 < X.σ) :
    ¬ ContinuousWithinAt (deriv W) (Ici (0 : ℝ)) 0 := by
  sorry
end AvramDividend.Classical
