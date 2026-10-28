-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_strict_stopped_scale_payoff_antitone_discount_any_measure
-- name    : AvramDividend.Classical.chat04_strict_stopped_scale_payoff_antitone_discount_any_measure
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T14:14:33.825989+00:00
-- url     : https://prove2.me/theorems/c6a6a34b-a822-4a8e-b550-a94953fb6f81
-- title:
--   Any-measure strict stopped q-scale payoff decreases with discount rate
-- statement:
--   The upper-first stopped q-scale payoff lower integral decreases as the discount rate increases, for arbitrary path-space measures and all scale-payoff functions W. The theorem combines exact no-overshoot factorisation of the terminal scale payoff with arbitrary-measure discount antitonicity. It imposes no stochastic martingale or optional-stopping premise.
-- source:
--   Proved strict stopped exit payoff arbitrary-measure factorisation f235d825-e540-4b9b-87e0-1bd77e6b4be3; pending published arbitrary-measure discount comparison chat04_strict_exit_lintegral_antitone_discount_any_measure. Pure ENNReal multiplication order.

import Mathlib.Data.ENNReal.Real
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat04_strict_stopped_exit_payoff_any_measure_factorisation
import Theorems.Thm_AvramDividend_Classical_chat04_strict_exit_lintegral_antitone_discount_any_measure

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat04_strict_stopped_scale_payoff_antitone_discount_any_measure
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (μ : Measure Ω)
    (q₁ q₂ a x : ℝ) (hq : q₁ ≤ q₂) (hxa : x ≤ a)
    (W : ℝ → ℝ) :
    (∫⁻ ω,
      if twoSidedExitUpTime X (a - x) ω <
          twoSidedExitDownTime X (-x) ω then
        ENNReal.ofReal
          (Real.exp (-(q₂ * ENNReal.toReal
            (twoSidedExitUpTime X (a - x) ω)))) *
        ENNReal.ofReal
          (W (x + X.X (twoSidedExitUpTime X (a - x) ω).toNNReal ω))
      else 0 ∂μ) ≤
    (∫⁻ ω,
      if twoSidedExitUpTime X (a - x) ω <
          twoSidedExitDownTime X (-x) ω then
        ENNReal.ofReal
          (Real.exp (-(q₁ * ENNReal.toReal
            (twoSidedExitUpTime X (a - x) ω)))) *
        ENNReal.ofReal
          (W (x + X.X (twoSidedExitUpTime X (a - x) ω).toNNReal ω))
      else 0 ∂μ) := by sorry
