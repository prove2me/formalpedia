-- Prove2me | Theorems.Thm_AvramDividend_Classical_vcstar_near_HJB_of_explicit_value_threshold
-- name    : AvramDividend.Classical.vcstar_near_HJB_of_explicit_value_threshold
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T10:52:23.441556+00:00
-- url     : https://prove2.me/theorems/7a07cab1-aa5b-422a-9a7e-b503cc35b70f
-- title:
--   Exact near-barrier dividend HJB beyond the explicit drift and unit-value thresholds
-- statement:
--   For a positive canonical barrier a of a C1 scale function with positive derivative minimised at a, define the barrier value v(a). At every x>a satisfying x≥a+max(0,c/q,1−v(a)), the full nonlocal Lévy generator of v exists and the exact dividend HJB maximum equals zero. The affine upper branch gives v(x)=x−a+v(a), so the explicit threshold guarantees the value floor v(x)≥1 and discounted drift domination. This eliminates the pointwise unit-value hypothesis from a previously proved nonlocal theorem. The result is conditional on the genuine regularity and minimisation hypotheses and is not an unconditional global verification statement.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.vcstar_near_HJB_of_explicit_value_threshold
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
    (hthreshold : (cstar W).toReal +
      max 0 (max (X.c / q) (1 - vcstar W (cstar W).toReal)) ≤ x) :
    X.GeneratorIntegrable (vcstar W) x ∧
      max (X.generator (vcstar W) x - q * vcstar W x)
        (1 - deriv (vcstar W) x) = 0 := by sorry
