-- Prove2me | Theorems.Thm_AvramDividend_Classical_vcstar_unrestricted_verification_regularity
-- name    : AvramDividend.Classical.vcstar_unrestricted_verification_regularity
-- status  : Open
-- author  : @WillR
-- created : 2026-10-07T22:35:29.372903+00:00
-- url     : https://prove2.me/theorems/ffdd6f8d-a5cc-4aee-8726-785404cd72f2
-- title:
--   Boundary and smoothness package for unrestricted verification of vcstar
-- statement:
--   Global continuity, zero-extension, nonnegativity and BV/unbounded-variation smoothness of the candidate vcstar on (0,∞), including the join at the optimal barrier. These are exactly the regularity hypotheses needed when applying Proposition 4(i) with cap C=∞, under the smoothness alternatives of Theorem 2. The c*=0 case is affine on the entire positive half-line.
-- source:
--   Avram, Palmowski and Pistorius (2007), scale-function regularity under condition (3.3), Theorem 2 and Proposition 4(i), pp. 5, 14-20.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

namespace AvramDividend.Classical
theorem vcstar_unrestricted_verification_regularity
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤)
    (h_smooth : 0 < X.σ ∨ X.BoundedVariation ∨ ContDiffOn ℝ 2 (vcstar W) (Ioi 0)) :
    ContinuousOn (vcstar W) (Ici 0) ∧
      0 ≤ vcstar W 0 ∧
      (∀ y < 0, vcstar W y = 0) ∧
      ((¬ X.BoundedVariation → ContDiffOn ℝ 2 (vcstar W) (Ioi 0)) ∧
       (X.BoundedVariation → ContDiffOn ℝ 1 (vcstar W) (Ioi 0))) := by
  sorry
end AvramDividend.Classical
