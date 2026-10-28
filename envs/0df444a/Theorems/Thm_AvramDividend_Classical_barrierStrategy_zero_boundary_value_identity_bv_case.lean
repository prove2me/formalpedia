-- Prove2me | Theorems.Thm_AvramDividend_Classical_barrierStrategy_zero_boundary_value_identity_bv_case
-- name    : AvramDividend.Classical.barrierStrategy_zero_boundary_value_identity_bv_case
-- status  : Open
-- author  : @WillR
-- created : 2026-10-27T12:23:56.068673+00:00
-- url     : https://prove2.me/theorems/dde53f36-4854-400f-8c80-8ca15d7a0092
-- title:
--   Zero-barrier boundary identity under bounded variation
-- statement:
--   Under Standing and bounded variation, the zero-barrier dividend value at zero reserve equals the scale-function barrier value at zero. This isolates the bounded-variation branch of barrierStrategy_zero_boundary_value_identity (c2921c8c), whose unbounded-variation branch already reduces to Proved fd11e610 via Open 4502f364; the remaining work is the ruinTime/paymentTimes-at-zero computation recorded in the parent derivation.
-- source:
--   BV-branch decomposition of c2921c8c (barrierStrategy_zero_boundary_value_identity): case split by X.BoundedVariation recorded 2026-10-27 with exact authoritative unfoldings of barrierStrategy/dividendValue/barrierValue at zero

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

namespace AvramDividend.Classical

theorem barrierStrategy_zero_boundary_value_identity_bv_case
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hBV : X.BoundedVariation) :
    dividendValue X q 0 (barrierStrategy X 0 0) =
      ENNReal.ofReal (barrierValue W 0 0) := by sorry

end AvramDividend.Classical
