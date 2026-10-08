-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_shifted_kernel_gap_on_halfline_canonical
-- name    : AvramDividend.Classical.bv_shifted_kernel_gap_on_halfline_canonical
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T06:29:06.936514+00:00
-- url     : https://prove2.me/theorems/ca920c60-c67e-444f-855e-85bda191e74d
-- title:
--   The canonical BV shifted kernel remains contractive on a whole Laplace half-line
-- statement:
--   There is a positive anchor b such that for every s≥b, the positive jump-magnitude renewal-kernel transform shifted by the canonical Esscher value q/X.drift is strictly below the BV drift. The result is the canonical-witness version of Laplace monotonicity of the supported positive kernel and is designed to compose directly with the scale-denominator theorem.
-- source:
--   Proved bv_supported_positive_kernel_transform_gap and bv_standing_drift_pos.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_shifted_kernel_gap_on_halfline_canonical
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (hbv : X.BoundedVariation) :
    ∃ b : ℝ, 0 < b ∧
      ∀ s : ℝ, b ≤ s →
        (∫⁻ z : ℝ≥0, ENNReal.ofReal
          ((1 - Real.exp (-(s + q / X.drift) * (z : ℝ))) / s)
          ∂(X.ν.map (fun y : ℝ => Real.toNNReal (-y)))) <
          ENNReal.ofReal X.drift := by sorry
