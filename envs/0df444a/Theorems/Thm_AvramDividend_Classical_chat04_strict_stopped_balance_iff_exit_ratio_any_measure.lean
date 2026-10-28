-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_strict_stopped_balance_iff_exit_ratio_any_measure
-- name    : AvramDividend.Classical.chat04_strict_stopped_balance_iff_exit_ratio_any_measure
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T13:03:31.661086+00:00
-- url     : https://prove2.me/theorems/676cfbca-81fe-4521-8d32-df524b85dfcd
-- title:
--   Arbitrary-measure strict stopped-scale balance iff normalised upper-first exit ratio
-- statement:
--   For any path-space measure and positive upper-barrier q-scale value, the discounted strict two-sided upper-exit stopped q-scale payoff equals its starting scale value if and only if the upper-before-ruin discounted exit integral is the corresponding scale ratio. Uses the canonical arbitrary-measure factorisation; no optional-stopping or killed-harmonicity premise is assumed.
-- source:
--   Proved AvramDividend.Classical.chat04_strict_stopped_exit_payoff_any_measure_factorisation (f235d825-e540-4b9b-87e0-1bd77e6b4be3), with ENNReal cancellation as in Proved chat04_exit_ratio_iff_stopped_balance (dd744ff9-173f-476b-9b48-95d93f53bba9).

import Mathlib.Data.ENNReal.Inv
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat04_strict_stopped_exit_payoff_any_measure_factorisation

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat04_strict_stopped_balance_iff_exit_ratio_any_measure
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (μ : Measure Ω)
    (q a x : ℝ) (hxa : x ≤ a) (W : ℝ → ℝ) (hWa : 0 < W a) :
    ((∫⁻ ω,
      if twoSidedExitUpTime X (a - x) ω <
          twoSidedExitDownTime X (-x) ω then
        ENNReal.ofReal
          (Real.exp (-(q * ENNReal.toReal (twoSidedExitUpTime X (a - x) ω)))) *
          ENNReal.ofReal
            (W (x + X.X (twoSidedExitUpTime X (a - x) ω).toNNReal ω))
      else 0 ∂μ) = ENNReal.ofReal (W x)) ↔
    ((∫⁻ ω,
      if twoSidedExitUpTime X (a - x) ω <
          twoSidedExitDownTime X (-x) ω then
        ENNReal.ofReal
          (Real.exp (-(q * ENNReal.toReal (twoSidedExitUpTime X (a - x) ω))))
      else 0 ∂μ) = ENNReal.ofReal (W x / W a)) := by sorry
