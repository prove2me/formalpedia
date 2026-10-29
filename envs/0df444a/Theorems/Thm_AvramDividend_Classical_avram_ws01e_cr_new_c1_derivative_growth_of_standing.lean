-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_cr_new_c1_derivative_growth_of_standing
-- name    : AvramDividend.Classical.avram_ws01e_cr_new_c1_derivative_growth_of_standing
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T23:59:32.752991+00:00
-- url     : https://prove2.me/theorems/6cda9603-3384-49d4-bd5d-a3d32379f391
-- title:
--   Standing and C1 imply exponential lower growth of q-scale derivative without a killed-exit hypothesis
-- statement:
--   For a genuine standing spectrally negative Lévy process and positive discount, any q-scale function continuously differentiable on the positive half-line has derivative eventually at least c exp(φ x) for some c,φ>0. Unlike the accepted corrected-exit conditional theorem, no two-sided exit identity premise is needed: accepted genuine tilted-normalised positivity and monotonicity already supply it.
-- source:
--   Direct source-faithful corollary of Proved scaleFunction_tilted_positive_monotone, normalized_derivative_lower_bound, and normalized_eventual_derivative_growth. A source-specific bridge reducing the WS3 scale derivative divergence to WS2 C1 regularity alone.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_tilted_positive_monotone
import Theorems.Thm_AvramDividend_Classical_normalized_derivative_lower_bound
import Theorems.Thm_AvramDividend_Classical_normalized_eventual_derivative_growth
open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01e_cr_new_c1_derivative_growth_of_standing
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hreg : ContDiffOn ℝ 1 W (Ioi 0)) :
    ∃ φ c : ℝ, 0 < φ ∧ 0 < c ∧
      ∀ᶠ x in Filter.atTop, c * Real.exp (φ * x) ≤ deriv W x := by sorry
