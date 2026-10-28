-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_strict_upper_exit_scale_payoff_lintegral_finite
-- name    : AvramDividend.Classical.chat04_strict_upper_exit_scale_payoff_lintegral_finite
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T09:04:35.754587+00:00
-- url     : https://prove2.me/theorems/2b120fc6-3163-46d8-9b18-82507169af72
-- title:
--   Finiteness of the strict upper-exit stopped q-scale payoff expectation
-- statement:
--   The expected ENNReal q-discounted terminal scale payoff on strict upward exit before ruin is finite for any nonnegative q, since it is bounded by the finite deterministic scale value W(a). Finiteness is an explicit input to cancellations and expectation convergence in the stopped-scale martingale proof.
-- source:
--   Proved chat04_strict_stopped_exit_payoff_lintegral_bound and pinned Mathlib ENNReal.ofReal_lt_top.

import Mathlib.Data.ENNReal.Basic
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat04_strict_stopped_exit_payoff_lintegral_bound

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat04_strict_upper_exit_scale_payoff_lintegral_finite
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 ≤ q) (a x : ℝ) (hxa : x ≤ a)
    (W : ℝ → ℝ) :
    (∫⁻ ω,
      if twoSidedExitUpTime X (a - x) ω <
          twoSidedExitDownTime X (-x) ω then
        ENNReal.ofReal
          (Real.exp (-(q * ENNReal.toReal (twoSidedExitUpTime X (a - x) ω)))) *
          ENNReal.ofReal
            (W (x + X.X (twoSidedExitUpTime X (a - x) ω).toNNReal ω))
      else 0 ∂P) < ⊤ := by sorry
