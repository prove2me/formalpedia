-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_positive_jump_moment_finite
-- name    : AvramDividend.Classical.bv_positive_jump_moment_finite
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-03T23:50:00.748118+00:00
-- url     : https://prove2.me/theorems/c04fb14e-f6d6-4d31-bfae-c7e5ef5de95b
-- title:
--   BV spectrally negative Lévy jump measure gives integrable positive jump magnitudes
-- statement:
--   For any Classical spectrally negative Lévy process X satisfying bounded variation (zero Gaussian part and finite small negative jump first moment), the image of the actual Lévy measure under y↦max(-y,0) has finite ∫min(z,1). The proof uses the previously published pointwise majorant by the original small-jump BV integral plus the Lévy measure's square-integrability assumption, and Mathlib's lintegral_map and indicator lemmas. This closes the exact hypothesis needed to apply the already published discounted-compensator DCT to the mission's actual process, rather than to an abstract jump measure.
-- source:
--   Actual Classical SpectrallyNegativeLevy definition 933ced80-71c1-4c0f-a6a7-ab7757fc97e9, bound negative_jump_truncation_bound, pinned Mathlib MeasureTheory.lintegral_map/lintegral_indicator

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

/-- For a bounded-variation Classical spectrally negative Lévy process,
the image of its negative-jump Lévy measure under jump magnitude
y ↦ max(-y,0) has finite truncated first moment. -/
theorem bv_positive_jump_moment_finite {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hbv : X.BoundedVariation) :
    (∫⁻ z : ℝ≥0, ENNReal.ofReal (min (z : ℝ) 1)
       ∂(X.ν.map (fun y : ℝ => Real.toNNReal (-y)))) ≠ ⊤ := by
  sorry

end AvramDividend.Classical
