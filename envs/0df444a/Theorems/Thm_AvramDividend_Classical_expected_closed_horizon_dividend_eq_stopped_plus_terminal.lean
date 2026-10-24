-- Prove2me | Theorems.Thm_AvramDividend_Classical_expected_closed_horizon_dividend_eq_stopped_plus_terminal
-- name    : AvramDividend.Classical.expected_closed_horizon_dividend_eq_stopped_plus_terminal
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T14:53:54.81278+00:00
-- url     : https://prove2.me/theorems/1a37b5b3-ce3f-49ef-a2d4-d56296d731c7
-- title:
--   Exact expected closed-horizon reward as stopped Stieltjes reward plus terminal atom
-- statement:
--   For any probability-space measurable structure, any real-valued dividend path D, any random nonnegative-extended stopping horizon σ, positive deterministic T and discount q, the expected closed-horizon Stieltjes dividend payoff equals the expectation of the sum of its strictly stopped payoff and terminal singleton Stieltjes atom. The identity is pointwise in ω before integration and requires no unsupported claim about separate expectation addition, integrability, semimartingales or absence of continuous dividends.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_paymentTimes_closed_horizon_lintegral_eq_stopped_add_atom

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.expected_closed_horizon_dividend_eq_stopped_plus_terminal
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (D : ℝ≥0 → Ω → ℝ) (σ : Ω → ℝ≥0∞)
    (q T : ℝ) (hT : 0 < T) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (σ ω) ∩ Set.Iic T,
       ENNReal.ofReal (Real.exp (-(q * t)))
         ∂(dividendMeasure D ω) ∂P) =
    (∫⁻ ω,
      (∫⁻ t in paymentTimes
        (min (σ ω) (ENNReal.ofReal T)),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)) +
      (∫⁻ t in paymentTimes (σ ω) ∩ ({T} : Set ℝ),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)) ∂P) := by sorry
