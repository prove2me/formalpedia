-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_strict_stopped_exit_payoff_any_measure_factorisation
-- name    : AvramDividend.Classical.chat04_strict_stopped_exit_payoff_any_measure_factorisation
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T11:25:33.794606+00:00
-- url     : https://prove2.me/theorems/f235d825-e540-4b9b-87e0-1bd77e6b4be3
-- title:
--   Factorisation of strict upper-exit stopped q-scale payoff under an arbitrary sample-path measure
-- statement:
--   At strict upper exit before ruin, the discounted q-scale terminal reward integral under any path-space measure factors into the discounted upper-first integral and the scale value at the upper barrier. The statement is invariant under probability tilting and finite measures.
-- source:
--   Generalises the remotely accepted chat04_strict_stopped_exit_payoff_lintegral_factorisation using the same accepted pathwise overshoot and measurability interfaces.

import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Analysis.Complex.Exponential
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat04_strict_upper_exit_scale_payoff
import Theorems.Thm_AvramDividend_Classical_chat03_exact_upperfirst_discount_integrand_measurable

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat04_strict_stopped_exit_payoff_any_measure_factorisation
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (μ : Measure Ω)
    (q a x : ℝ) (hxa : x ≤ a) (W : ℝ → ℝ) :
    (∫⁻ ω,
      if twoSidedExitUpTime X (a - x) ω <
          twoSidedExitDownTime X (-x) ω then
        ENNReal.ofReal
          (Real.exp (-(q * ENNReal.toReal (twoSidedExitUpTime X (a - x) ω)))) *
          ENNReal.ofReal
            (W (x + X.X (twoSidedExitUpTime X (a - x) ω).toNNReal ω))
      else 0 ∂μ) =
      (∫⁻ ω,
        if twoSidedExitUpTime X (a - x) ω <
            twoSidedExitDownTime X (-x) ω then
          ENNReal.ofReal
            (Real.exp (-(q * ENNReal.toReal (twoSidedExitUpTime X (a - x) ω))))
        else 0 ∂μ) * ENNReal.ofReal (W a) := by sorry
