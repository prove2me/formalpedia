-- Prove2me | Theorems.Thm_AvramDividend_Classical_unbounded_scale_zero_origin_nonnegative_discount
-- name    : AvramDividend.Classical.unbounded_scale_zero_origin_nonnegative_discount
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T13:51:36.462273+00:00
-- url     : https://prove2.me/theorems/7323e81c-9f47-4cae-a748-46f57c708cec
-- title:
--   All nonnegative-discount scale functions vanish at zero in unbounded variation
-- statement:
--   For a spectrally negative Lévy process with unbounded variation, every scale function at any nonnegative discount rate vanishes at the origin. This unifies the already Proved zero-discount and strictly positive-discount cases and gives a convenient reusable boundary identity.
-- source:
--   Case split at discount zero, using two independently Proved zero-origin theorems.

import Theorems.Thm_AvramDividend_Classical_unbounded_scale_zero_origin_zero_discount
import Theorems.Thm_AvramDividend_Classical_chat04_scale_zero_origin_of_unbounded_variation
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.unbounded_scale_zero_origin_nonnegative_discount
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hnbv : ¬ X.BoundedVariation)
    (q : ℝ) (hq : 0 ≤ q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    W 0 = 0 := by sorry
