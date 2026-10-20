-- Prove2me | Theorems.Thm_AvramDividend_Classical_vcstar_discounted_value_dominates_drift_at_threshold
-- name    : AvramDividend.Classical.vcstar_discounted_value_dominates_drift_at_threshold
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T13:14:12.23489+00:00
-- url     : https://prove2.me/theorems/f1a24362-066e-4106-85c9-6274979763e8
-- title:
--   Sharp right-barrier discounted-value threshold for drift domination
-- statement:
--   For a formal q-scale function W, positive q and positive finite canonical barrier a, on the strict right branch x>a, the discounted dividend value q*vcstar W x dominates the Lévy drift coefficient X.c whenever x≥a+max(0,X.c/q). Unlike the previously Proved far-field bound, there is no unnecessary extra unit of reserve. The exact affine branch is x-a+W(a)/W'(a), and the intercept is nonnegative even under totalised zero denominators by monotonicity of W and nonnegative derivative. This is a strict mathematical improvement needed to bring the nonlocal HJB inequality closer to the barrier.

import Mathlib.Tactic.Linarith
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_deriv_nonneg_of_pos

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.vcstar_discounted_value_dominates_drift_at_threshold
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hpos : 0 < (cstar W).toReal)
    (x : ℝ)
    (hx : (cstar W).toReal < x)
    (hthreshold : (cstar W).toReal + max 0 (X.c / q) ≤ x) :
    X.c ≤ q * vcstar W x := by sorry
