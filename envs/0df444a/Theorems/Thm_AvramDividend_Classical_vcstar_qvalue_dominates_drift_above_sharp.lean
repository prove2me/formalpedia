-- Prove2me | Theorems.Thm_AvramDividend_Classical_vcstar_qvalue_dominates_drift_above_sharp
-- name    : AvramDividend.Classical.vcstar_qvalue_dominates_drift_above_sharp
-- status  : Open
-- author  : @WillR
-- created : 2026-10-19T13:11:04.022676+00:00
-- url     : https://prove2.me/theorems/fe356583-4478-4e02-a2c3-904ffe89cb1e
-- title:
--   Sharp above-barrier discounted value bound without an extra unit of capital
-- statement:
--   For any positive discount q, a genuine q-scale function W, and a strictly positive real dividend barrier a, every x>a satisfying x≥a+max(0,X.c/q) obeys X.c≤q*vcstar W x. The proof uses nonnegativity of the scaled endpoint value W(a)/W'(a), even under totalised zero division, and the exact affine branch vcstar W x=x−a+W(a)/W'(a). This sharpens the previously Proved far-field comparison by removing the unnecessary extra unit of capital, enabling a tighter nonlocal HJB region when the affine-majorant condition controls crossing jumps.

import Mathlib.Tactic.Linarith
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.vcstar_qvalue_dominates_drift_above_sharp
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hpos : 0 < (cstar W).toReal)
    (x : ℝ) (hx : (cstar W).toReal < x)
    (hthreshold : (cstar W).toReal + max 0 (X.c / q) ≤ x) :
    X.c ≤ q * vcstar W x := by sorry
