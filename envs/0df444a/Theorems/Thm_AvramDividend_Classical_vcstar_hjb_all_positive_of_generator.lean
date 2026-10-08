-- Prove2me | Theorems.Thm_AvramDividend_Classical_vcstar_hjb_all_positive_of_generator
-- name    : AvramDividend.Classical.vcstar_hjb_all_positive_of_generator
-- status  : Open
-- author  : @WillR
-- created : 2026-10-07T22:35:41.605457+00:00
-- url     : https://prove2.me/theorems/edf09308-1b7f-449e-ac5d-ae6f22d385c3
-- title:
--   Candidate satisfies HJB for every positive reserve under the above-barrier condition
-- statement:
--   Assemble the classical HJB pointwise equality on the entire positive real half-line from the generator equality below the positive barrier, the supplied generator inequality and affine derivative above the barrier, and the separate at-barrier compatibility lemma. For c*=0, every y>0 is in the above-barrier branch, so no at-barrier premise is required. This is the HJB package needed by global verification with C=∞.
-- source:
--   Avram, Palmowski and Pistorius (2007), Theorem 2(ii), equation (5.8) and Proposition 4(i), pp. 14-21.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

namespace AvramDividend.Classical
theorem vcstar_hjb_all_positive_of_generator
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤)
    (h_smooth : 0 < X.σ ∨ X.BoundedVariation ∨ ContDiffOn ℝ 2 (vcstar W) (Ioi 0))
    (hgen : ∀ y : ℝ, (cstar W).toReal < y →
      X.GeneratorIntegrable (vcstar W) y ∧
        X.generator (vcstar W) y - q * vcstar W y ≤ 0) :
    ∀ y : ℝ, 0 < y →
      X.GeneratorIntegrable (vcstar W) y ∧
        max (X.generator (vcstar W) y - q * vcstar W y)
            (1 - deriv (vcstar W) y) = 0 := by
  sorry
end AvramDividend.Classical
