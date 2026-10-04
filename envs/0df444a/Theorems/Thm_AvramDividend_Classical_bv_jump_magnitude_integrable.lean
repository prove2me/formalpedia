-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_jump_magnitude_integrable
-- name    : AvramDividend.Classical.bv_jump_magnitude_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-03T22:56:32.733465+00:00
-- url     : https://prove2.me/theorems/47ec8f0a-2814-464f-b8b0-6337c03825bc
-- title:
--   Finite truncated first moment for the positive jump-magnitude measure of a BV Lévy process
-- statement:
--   Let X be a bounded-variation spectrally negative Lévy process with canonical measure ν. Map its negative-jump Lévy measure restricted to (-∞,0) by the nonnegative magnitude y↦max(-y,0), obtaining a measure μ on nonnegative real jump sizes. Then ∫min(z,1) μ(dz) is finite. This is the exact stochastic-to-analytic adapter required before applying the previously prepared dominated-convergence and contractive renewal-kernel theorems.
-- source:
--   Canonical Classical SpectrallyNegativeLevy.ν_integrable and BoundedVariation.2; pinned Mathlib lintegral_map and Real.coe_toNNReal

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

/-- A BV spectrally negative Lévy process has a positive-jump-magnitude
pushforward measure with finite truncated first moment. -/
theorem bv_jump_magnitude_integrable {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation) :
    (∫⁻ z : ℝ≥0, ENNReal.ofReal (min (z : ℝ) 1)
      ∂ ((X.ν.restrict (Iio (0 : ℝ))).map
          (fun y : ℝ => Real.toNNReal (-y)))) < ⊤ := by
  sorry

end AvramDividend.Classical
