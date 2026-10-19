-- Prove2me | Theorems.Thm_AvramDividend_Classical_vcstar_qvalue_dominates_drift_far_positive_barrier
-- name    : AvramDividend.Classical.vcstar_qvalue_dominates_drift_far_positive_barrier
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T10:25:35.280602+00:00
-- url     : https://prove2.me/theorems/80dc6cff-dff4-4d5a-ba43-eb85005f88c2
-- title:
--   At sufficiently high reserves the discounted dividend barrier value dominates the Lévy drift
-- statement:
--   For any positive discount rate q, an exact q-scale function W with a strictly positive real optimal barrier a, and x at least a+1+max(0,X.c/q), the discounted candidate q*vcstar W x exceeds or equals the drift coefficient X.c. The positivity of W(a) and nonnegative ordinary derivative W'(a) make the scale-function continuation intercept nonnegative (with totalised real division also handling W'(a)=0). Since above a the candidate is x-a+intercept, q times its linear growth eventually dominates any finite drift. This gives the q-value comparison required by the separate genuine nonlocal far-field HJB generator inequality.

import Mathlib.Tactic.Linarith
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.vcstar_qvalue_dominates_drift_far_positive_barrier
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hpos : 0 < (cstar W).toReal)
    (x : ℝ)
    (hfar : (cstar W).toReal + 1 + max 0 (X.c / q) ≤ x) :
    X.c ≤ q * vcstar W x := by sorry
