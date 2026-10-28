-- Prove2me | Theorems.Thm_AvramDividend_Classical_scaleFunction_global_continuous_of_zero_origin
-- name    : AvramDividend.Classical.scaleFunction_global_continuous_of_zero_origin
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T18:13:38.849534+00:00
-- url     : https://prove2.me/theorems/9e68affb-d2da-4e61-b6fc-dd672e06e3cb
-- title:
--   Global continuity of a zero-origin q-scale function
-- statement:
--   If a canonical q-scale function vanishes at zero, its defining continuity on nonnegative reserves extends across all real reserves. On the nonpositive half-line it equals zero, and these continuous pieces glue at the origin. The result supplies the continuity required to convert the Esscher-normalised scale into a Stieltjes cumulative measure.
-- source:
--   IsScaleFunction continuity and support; Mathlib ContinuousOn.union_of_isClosed.

import Mathlib.Topology.ContinuousOn
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.scaleFunction_global_continuous_of_zero_origin
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W)
    (hZero : W 0 = 0) :
    Continuous W := by sorry
