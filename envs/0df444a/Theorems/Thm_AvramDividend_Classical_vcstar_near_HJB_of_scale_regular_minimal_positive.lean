-- Prove2me | Theorems.Thm_AvramDividend_Classical_vcstar_near_HJB_of_scale_regular_minimal_positive
-- name    : AvramDividend.Classical.vcstar_near_HJB_of_scale_regular_minimal_positive
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T14:17:29.950565+00:00
-- url     : https://prove2.me/theorems/9a7428e0-1d1f-4f38-b774-d8a70f5e56ad
-- title:
--   Full near-barrier HJB from scale regularity and positive derivative minimum
-- statement:
--   Given an exact pinned q-scale function, q>0, a positive real canonical barrier, C1 scale regularity on positive reserves, a strictly positive scale derivative with global minimum at the barrier, the dividend value satisfies the exact Lévy generator-domain condition and full HJB maximum identity at all x above the barrier with x≥1 and x≥a+max(0,c/q). Unlike the earlier theorem, this statement does not separately assume continuity of the dividend value on [0,a]: that continuity is now a Proved direct consequence of IsScaleFunction. The result combines two accepted proofs and does not claim the difficult unconditioned global scale-function q-harmonicity.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.vcstar_near_HJB_of_scale_regular_minimal_positive
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
    (x : ℝ) (hx : (cstar W).toReal < x) (hx1 : 1 ≤ x)
    (hthreshold : (cstar W).toReal + max 0 (X.c / q) ≤ x) :
    X.GeneratorIntegrable (vcstar W) x ∧
      max (X.generator (vcstar W) x - q * vcstar W x)
        (1 - deriv (vcstar W) x) = 0 := by sorry
