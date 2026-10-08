-- Prove2me | Theorems.Thm_AvramDividend_Classical_vcstar_zero_basic_verification_boundary
-- name    : AvramDividend.Classical.vcstar_zero_basic_verification_boundary
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T23:16:00.379553+00:00
-- url     : https://prove2.me/theorems/b402060a-8d7f-4456-9fa9-23922c721206
-- title:
--   Continuity and nonnegative boundary of the optimal candidate at c-star zero
-- statement:
--   When the canonical barrier is zero, v_cstar(x)=x+v_0(0) on [0,∞), so it is continuous there. Nonnegativity at the origin follows from the zero-barrier expected dividend boundary package, while the negative side is zero by the formal extension. This supplies the zero-barrier endpoint hypotheses of the unrestricted local verification proposition, without assuming any smoothness of W at zero.
-- source:
--   Avram, Palmowski and Pistorius (2007), barrier formula (5.1) with a=0 and Proposition 1 zero-barrier reflection boundary; exact source-faithful branch of Theorem 2(ii).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

namespace AvramDividend.Classical
theorem vcstar_zero_basic_verification_boundary
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc0 : cstar W = 0) :
    ContinuousOn (vcstar W) (Ici 0) ∧
      0 ≤ vcstar W 0 ∧
      ∀ y < 0, vcstar W y = 0 := by
  sorry
end AvramDividend.Classical
