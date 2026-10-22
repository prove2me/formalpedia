-- Prove2me | Theorems.Thm_AvramDividend_Classical_vcstar_near_HJB_of_unit_value_regular_minimum
-- name    : AvramDividend.Classical.vcstar_near_HJB_of_unit_value_regular_minimum
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T06:52:17.867714+00:00
-- url     : https://prove2.me/theorems/3d8774e9-6a3c-41d3-97c5-b268d72e7589
-- title:
--   Exact near-barrier dividend HJB under positive regular minimality and a unit value floor
-- statement:
--   For a strictly positive canonical cap of a regular q-scale function W, assume C1 regularity of W on positive reserves, positive ordinary scale derivative, and global minimisation of that derivative at cstar. At any reserve x strictly above the cap where the value satisfies v(x)≥1 and x≥cap+max(0,c/q), the full nonlocal Lévy generator exists and the exact max-form dividend HJB equation is zero. The proof derives the left affine-majorant from the derivative minimum and uses the unit-value ruin-crossing jump inequality, permitting some reserves x<1. The conditions are explicitly stated; the theorem is not an unconditional global HJB claim.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.vcstar_near_HJB_of_unit_value_regular_minimum
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hreg : ContDiffOn ℝ 1 W (Ioi 0))
    (hpositive : ∀ z : ℝ, 0 < z → 0 < deriv W z)
    (hbarrier : 0 < (cstar W).toReal)
    (hminimal : ∀ z : ℝ, 0 < z →
      deriv W (cstar W).toReal ≤ deriv W z)
    (x : ℝ) (hx : (cstar W).toReal < x)
    (hunit : 1 ≤ vcstar W x)
    (hthreshold : (cstar W).toReal + max 0 (X.c / q) ≤ x) :
    X.GeneratorIntegrable (vcstar W) x ∧
      max (X.generator (vcstar W) x - q * vcstar W x)
        (1 - deriv (vcstar W) x) = 0 := by sorry
