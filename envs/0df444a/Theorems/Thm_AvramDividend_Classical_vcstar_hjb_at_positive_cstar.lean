-- Prove2me | Theorems.Thm_AvramDividend_Classical_vcstar_hjb_at_positive_cstar
-- name    : AvramDividend.Classical.vcstar_hjb_at_positive_cstar
-- status  : Open
-- author  : @WillR
-- created : 2026-10-07T22:35:36.400988+00:00
-- url     : https://prove2.me/theorems/8d03da6b-9d29-480a-8905-4d21edfcdaaf
-- title:
--   HJB pointwise identity at a strictly positive finite c-star
-- statement:
--   The HJB equation at the finite strictly positive optimal barrier. The existing Lemma 4 proves generator equality strictly below c*, while the extra hypothesis proves nonpositivity strictly above it. This endpoint lemma expresses the required limiting/smooth-fit argument, including generator integrability, without mistakenly using a strict hypothesis at equality.
-- source:
--   Avram, Palmowski and Pistorius (2007), Lemma 4 and Theorem 2(ii), smooth fit at the optimal barrier, HJB (5.8), pp. 14-21.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

namespace AvramDividend.Classical
theorem vcstar_hjb_at_positive_cstar
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤)
    (h_smooth : 0 < X.σ ∨ X.BoundedVariation ∨ ContDiffOn ℝ 2 (vcstar W) (Ioi 0))
    (hcpos : 0 < cstar W)
    (hgen : ∀ y : ℝ, (cstar W).toReal < y →
      X.GeneratorIntegrable (vcstar W) y ∧
        X.generator (vcstar W) y - q * vcstar W y ≤ 0) :
    X.GeneratorIntegrable (vcstar W) (cstar W).toReal ∧
      max (X.generator (vcstar W) (cstar W).toReal -
           q * vcstar W (cstar W).toReal)
          (1 - deriv (vcstar W) (cstar W).toReal) = 0 := by
  sorry
end AvramDividend.Classical
