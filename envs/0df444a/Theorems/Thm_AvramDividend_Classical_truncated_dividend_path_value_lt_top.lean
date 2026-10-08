-- Prove2me | Theorems.Thm_AvramDividend_Classical_truncated_dividend_path_value_lt_top
-- name    : AvramDividend.Classical.truncated_dividend_path_value_lt_top
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T21:18:43.490466+00:00
-- url     : https://prove2.me/theorems/666851fd-4032-4e27-8bcb-6bf83bc309f5
-- title:
--   Finite-horizon discounted dividend payoff is finite pathwise
-- statement:
--   For any dividend strategy, nonnegative discount rate and finite nonnegative deterministic horizon T, the pathwise discounted Stieltjes dividend integral over payment times up to T is finite. The payment set lies inside the bounded interval (-1,T], the associated Stieltjes dividend measure has finite mass there because its interval mass is an ENNReal.ofReal of a finite right-limit difference, and the discount factor is at most one on nonnegative payment times.
-- source:
--   Measure-theoretic helper for Proposition 4(i), enabling the finite-horizon ENNReal dividend payoff to be converted soundly to a real value with ENNReal.toReal.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.truncated_dividend_path_value_lt_top
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (q : ℝ) (hq : 0 ≤ q) (σ : ℝ≥0∞)
    (T : ℝ) (hT : 0 ≤ T) (ω : Ω) :
    (∫⁻ t in paymentTimes σ ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) < ∞ := by sorry
