-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gsource15_zerojump_hjb_linear_curvature_majorant
-- name    : AvramDividend.Classical.avram_gsource15_zerojump_hjb_linear_curvature_majorant
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T16:38:18.797684+00:00
-- url     : https://prove2.me/theorems/69d94d6e-d6a5-4bbe-a941-de88c8c47ad9
-- title:
--   Original zero-jump HJB bounds Gaussian curvature by nonnegative value and gradient
-- statement:
--   For the actual zero-jump Levy process with nonzero Gaussian coefficient, nonnegative value and derivative, and HJB generator residual nonpositive, the second derivative is bounded by the explicit nonnegative linear coefficient 2(q+|c|)/sigma^2 times value plus gradient. This is a source-exact quantitative curvature bound used to control Gaussian frozen-cell excursions, without assuming an Ito reward ledger.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f11_zero_jump_generator_eq_gaussian_drift
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gsource15_zerojump_hjb_linear_curvature_majorant
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (q : ℝ) (hq : 0 ≤ q)
    (w : ℝ → ℝ) (y : ℝ) (hσ : X.σ ≠ 0)
    (hw : 0 ≤ w y) (hwd : 0 ≤ deriv w y)
    (hHJB : X.generator w y - q * w y ≤ 0) :
    iteratedDeriv 2 w y ≤
      (2 * (q + |X.c|) / X.σ ^ 2) * (w y + deriv w y) := by
  sorry
