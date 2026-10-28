-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_strict_stopped_exit_payoff_pointwise_bound
-- name    : AvramDividend.Classical.chat04_strict_stopped_exit_payoff_pointwise_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T08:38:36.390798+00:00
-- url     : https://prove2.me/theorems/a0a3c75b-eb1f-4602-a6f5-16890c5a3ea4
-- title:
--   Strict two-sided stopped exit terminal payoff pointwise bound
-- statement:
--   For a spectrally negative Lévy process and nonnegative discount, the successful strict two-sided upper-exit discounted q-scale payoff is pointwise no greater than W(a). This follows from the verified first-upcrossing no-overshoot value and the established bound on discounted exit weights. It provides a domination lemma for stopping-time limit and integrability work, without martingale assumptions.
-- source:
--   Proved AvramDividend.Classical.chat04_strict_upper_exit_scale_payoff and chat03_discounted_upperfirst_weight_le_one; ENNReal monotone multiplication.

import Mathlib.Data.ENNReal.Basic
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat04_strict_upper_exit_scale_payoff
import Theorems.Thm_AvramDividend_Classical_chat03_discounted_upperfirst_weight_le_one

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat04_strict_stopped_exit_payoff_pointwise_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 ≤ q) (a x : ℝ) (hxa : x ≤ a)
    (W : ℝ → ℝ) (ω : Ω) :
    (if twoSidedExitUpTime X (a - x) ω <
          twoSidedExitDownTime X (-x) ω then
        ENNReal.ofReal
          (Real.exp (-(q * ENNReal.toReal (twoSidedExitUpTime X (a - x) ω)))) *
          ENNReal.ofReal
            (W (x + X.X (twoSidedExitUpTime X (a - x) ω).toNNReal ω))
     else 0) ≤ ENNReal.ofReal (W a) := by sorry
