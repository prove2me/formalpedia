-- Prove2me | Theorems.Thm_AvramDividend_Classical_boundedVariation_min_one_abs_integrable
-- name    : AvramDividend.Classical.boundedVariation_min_one_abs_integrable
-- status  : Open
-- author  : @WillR
-- created : 2026-10-07T06:36:00.507249+00:00
-- url     : https://prove2.me/theorems/1f8249f1-4c55-4a8c-91df-cd677dacd4d9
-- title:
--   Bounded variation makes min(1,abs y) integrable on negative jumps
-- statement:
--   For a bounded-variation spectrally negative Lévy process, the weight min(1,|y|) is integrable over negative jumps. On (-1,0), it equals |y| and integrability is exactly the finite first-moment clause in BoundedVariation. On (-∞,-1], it equals 1, and finite mass follows from the ordinary Lévy condition ∫min(1,y²)dν<∞ because min(1,y²)=1 there.
-- source:
--   Direct consequence of the BoundedVariation and ν_integrable fields in Def_AvramDividend_Classical_SpectrallyNegativeLevy.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem boundedVariation_min_one_abs_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation) :
    IntegrableOn (fun y : ℝ => min 1 |y|) (Iio 0) X.ν := by sorry

end AvramDividend.Classical
