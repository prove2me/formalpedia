-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_strict_two_sided_terminal_payoff_pointwise_bound_of_Wzero
-- name    : AvramDividend.Classical.chat04_strict_two_sided_terminal_payoff_pointwise_bound_of_Wzero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T09:03:09.533583+00:00
-- url     : https://prove2.me/theorems/a60482f8-4b13-4e69-849e-1e40ed611251
-- title:
--   Pointwise domination of the strict two-sided stopped scale payoff when W(0) vanishes
-- statement:
--   For any path, the sum of the strict upper-exit and lower-ruin discounted q-scale terminal payoffs is bounded above by W(a) when q is non-negative, x≤a, and W(0)=0. The lower-ruin scale payoff vanishes pointwise, including creeping onto the zero boundary. This yields a uniform finite bound for the terminal stopped payoff, supporting subsequent dominated-convergence and optional-stopping arguments.
-- source:
--   Published chat04_lower_exit_scale_creeping_atom and chat04_strict_stopped_exit_payoff_pointwise_bound.

import Mathlib.Data.ENNReal.Basic
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat04_lower_exit_scale_creeping_atom
import Theorems.Thm_AvramDividend_Classical_chat04_strict_stopped_exit_payoff_pointwise_bound

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat04_strict_two_sided_terminal_payoff_pointwise_bound_of_Wzero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 ≤ q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) (hWzero : W 0 = 0)
    (a x : ℝ) (hxa : x ≤ a) (ω : Ω) :
    (if twoSidedExitUpTime X (a - x) ω <
          twoSidedExitDownTime X (-x) ω then
        ENNReal.ofReal
          (Real.exp (-(q * ENNReal.toReal (twoSidedExitUpTime X (a - x) ω)))) *
          ENNReal.ofReal
            (W (x + X.X (twoSidedExitUpTime X (a - x) ω).toNNReal ω))
      else 0) + (if twoSidedExitDownTime X (-x) ω <
          twoSidedExitUpTime X (a - x) ω then
        ENNReal.ofReal
          (Real.exp (-(q * ENNReal.toReal (twoSidedExitDownTime X (-x) ω)))) *
          ENNReal.ofReal
            (W (x + X.X (twoSidedExitDownTime X (-x) ω).toNNReal ω))
      else 0) ≤ ENNReal.ofReal (W a) := by sorry
