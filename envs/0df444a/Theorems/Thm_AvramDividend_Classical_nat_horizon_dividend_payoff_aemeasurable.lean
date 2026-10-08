-- Prove2me | Theorems.Thm_AvramDividend_Classical_nat_horizon_dividend_payoff_aemeasurable
-- name    : AvramDividend.Classical.nat_horizon_dividend_payoff_aemeasurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T06:35:32.191984+00:00
-- url     : https://prove2.me/theorems/74bea73a-dec8-4be0-abc1-89226fc2fb87
-- title:
--   A.e. measurability of deterministic-horizon discounted dividend payoffs
-- statement:
--   For an adapted left-continuous dividend strategy, the random discounted Stieltjes payoff accumulated before ruin and before each deterministic integer horizon is almost-everywhere measurable. This supplies the stochastic measurability hypothesis required for the outer monotone-convergence theorem.
-- source:
--   Measurability prerequisite implicit in the monotone-convergence passage after equation (5.13) of Avram, Palmowski and Pistorius (2007), Proposition 4(i).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.nat_horizon_dividend_payoff_aemeasurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D) :
    ∀ n : ℕ, AEMeasurable
      (fun ω => ∫⁻ t in
        paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) P := by sorry
