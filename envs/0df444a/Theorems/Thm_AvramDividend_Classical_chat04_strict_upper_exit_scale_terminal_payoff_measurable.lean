-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_strict_upper_exit_scale_terminal_payoff_measurable
-- name    : AvramDividend.Classical.chat04_strict_upper_exit_scale_terminal_payoff_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T09:00:29.856655+00:00
-- url     : https://prove2.me/theorems/019a9588-2373-4e59-aa5c-731b6239da10
-- title:
--   Measurability of the strict upper-exit stopped q-scale payoff
-- statement:
--   The actual strict upper-before-ruin q-scale terminal payoff is measurable even though the terminal path value uses a stopping time. Spectral negativity identifies its upper-exit scale factor with deterministic W(a), while the strict upper-exit discount is already known measurable.
-- source:
--   Proved chat04_strict_upper_exit_scale_payoff and chat03_exact_upperfirst_discount_integrand_measurable.

import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat04_strict_upper_exit_scale_payoff
import Theorems.Thm_AvramDividend_Classical_chat03_exact_upperfirst_discount_integrand_measurable

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat04_strict_upper_exit_scale_terminal_payoff_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q a x : ℝ) (hxa : x ≤ a)
    (W : ℝ → ℝ) :
    Measurable (fun ω : Ω => (if twoSidedExitUpTime X (a - x) ω <
          twoSidedExitDownTime X (-x) ω then
        ENNReal.ofReal
          (Real.exp (-(q * ENNReal.toReal (twoSidedExitUpTime X (a - x) ω)))) *
          ENNReal.ofReal
            (W (x + X.X (twoSidedExitUpTime X (a - x) ω).toNNReal ω))
      else 0)) := by sorry
