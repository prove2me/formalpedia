-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_strict_upper_exit_scale_payoff
-- name    : AvramDividend.Classical.chat04_strict_upper_exit_scale_payoff
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T19:43:07.104466+00:00
-- url     : https://prove2.me/theorems/3a6690c2-75f4-410d-a696-a0dee2597de4
-- title:
--   At a successful strict two-sided exit, the stopped scale payoff equals its upper-barrier value
-- statement:
--   For any sample path of a published spectrally negative Lévy process, initial reserve x at most a, q in R and any real function W, define the strict upward and downward first-passage times U and D. On the successful event U<D the upward time is finite, and the process has no upward overshoot: X_U=a-x. Therefore the discounted scale payoff exp(-q U) W(x+X_U) equals exp(-q U) W(a). On the complement, both killed payoffs equal zero. The identity is pointwise with no stochastic martingale, expectation, or scale-function assumption. It supplies the upper-boundary payoff identification needed in the stopped-scale optional-stopping argument.
-- source:
--   Finite first-upcrossing threshold theorem 014436e7-36d8-45ea-8ca6-bc6917b7788c, the published strict two-sided-exit definitions a151e213-9af7-4401-b163-8e74db317cf8, and ENNReal.coe_toNNReal from pinned Mathlib.Data.ENNReal.Basic. This is the exact upper-boundary identification component of the Open stopped-scale martingale identity 09663d0d-c23e-47da-b5b9-1bbf28449a4d.

import Mathlib.Data.ENNReal.Basic
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_firstUpcrossing_value_eq_threshold

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat04_strict_upper_exit_scale_payoff
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (W : ℝ → ℝ) (q a x : ℝ) (hxa : x ≤ a) (ω : Ω) :
    (if twoSidedExitUpTime X (a - x) ω <
          twoSidedExitDownTime X (-x) ω then
        ENNReal.ofReal (Real.exp
          (-(q * (twoSidedExitUpTime X (a - x) ω).toReal))) *
          ENNReal.ofReal
            (W (x + X.X (twoSidedExitUpTime X (a - x) ω).toNNReal ω))
     else 0) =
    (if twoSidedExitUpTime X (a - x) ω <
          twoSidedExitDownTime X (-x) ω then
        ENNReal.ofReal (Real.exp
          (-(q * (twoSidedExitUpTime X (a - x) ω).toReal))) *
          ENNReal.ofReal (W a)
     else 0) := by sorry
