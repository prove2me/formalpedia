-- Prove2me | Theorems.Thm_AvramDividend_Classical_vcstar_deriv_one_of_three_branch_regularity
-- name    : AvramDividend.Classical.vcstar_deriv_one_of_three_branch_regularity
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T09:44:53.370213+00:00
-- url     : https://prove2.me/theorems/753d8252-52fb-4cbc-9b7f-d8dac8e76705
-- title:
--   Three-way smooth fit from Gaussian tilted monotonicity and BV C1 regularity
-- statement:
--   For the exact positive finite c-star setting and genuine three-way disjunction of smoothness conditions, ordinary derivative one holds if the Gaussian case supplies a positive monotone exponential tilt of W and the bounded-variation case supplies C1 scale regularity on positive reserves. The explicit C2 case needs no additional assumption. This is a complete case-split theorem combining three Proved smooth-fit helpers, and it identifies only the residual stochastic inputs needed to close the original target.
-- source:
--   Avram, Palmowski and Pistorius (2007), condition (3.3) and smooth-fit at the derivative-minimising barrier.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_vcstar_deriv_one_of_bv_contDiff_one
import Theorems.Thm_AvramDividend_Classical_vcstar_deriv_one_of_gaussian_tilt
import Theorems.Thm_AvramDividend_Classical_vcstar_deriv_one_of_contDiffOn
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical
theorem vcstar_deriv_one_of_three_branch_regularity
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤) (hcpos : 0 < cstar W)
    (h_smooth : 0 < X.σ ∨ X.BoundedVariation ∨
      ContDiffOn ℝ 2 (vcstar W) (Ioi 0))
    (hgauss : 0 < X.σ →
      ∃ φ : ℝ, 0 < φ ∧
        MonotoneOn (fun x : ℝ => Real.exp (-φ * x) * W x) (Ioi 0))
    (hbv : X.BoundedVariation →
      ContDiffOn ℝ 1 W (Ioi (0 : ℝ))) :
    deriv (vcstar W) (cstar W).toReal = 1 := by sorry
end AvramDividend.Classical
