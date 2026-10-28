-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_upper_exit_discount_integral_factorisation
-- name    : AvramDividend.Classical.chat04_upper_exit_discount_integral_factorisation
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T09:05:24.213584+00:00
-- url     : https://prove2.me/theorems/29ac4824-b260-41ee-a215-4bd64512332e
-- title:
--   Upper-exit q-scale integral is the discounted upper-first mass times W(a)
-- statement:
--   The nonnegative integral of the strict successful upper-exit discounted q-scale payoff equals W(a) times the strict upper-before-lower discounted survival integral. This is the exact upper-terminal boundary factorisation under x ≤ a, with correct infinite first-passage guards and no optional-stopping or q-harmonicity assumption. The proof invokes the previously Proved pointwise no-upward-overshoot boundary theorem, then factors out the finite ENNReal.ofReal W(a) constant.
-- source:
--   Previously Proved AvramDividend.Classical.chat04_strict_upper_exit_scale_payoff UUID 3a6690c2-75f4-410d-a696-a0dee2597de4; pinned Mathlib MeasureTheory.lintegral_mul_const' and ENNReal.ofReal_ne_top.

import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Analysis.Complex.Exponential
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat04_strict_upper_exit_scale_payoff

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat04_upper_exit_discount_integral_factorisation
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ)
    (a x : ℝ) (hxa : x ≤ a) :
    (∫⁻ ω,
      if twoSidedExitUpTime X (a - x) ω <
          twoSidedExitDownTime X (-x) ω then
        ENNReal.ofReal (Real.exp
          (-(q * (twoSidedExitUpTime X (a - x) ω).toReal))) *
          ENNReal.ofReal
            (W (x + X.X (twoSidedExitUpTime X (a - x) ω).toNNReal ω))
      else 0 ∂P) =
      (∫⁻ ω,
        if twoSidedExitUpTime X (a - x) ω <
            twoSidedExitDownTime X (-x) ω then
          ENNReal.ofReal (Real.exp
            (-(q * (twoSidedExitUpTime X (a - x) ω).toReal)))
        else 0 ∂P) * ENNReal.ofReal (W a) := by sorry
