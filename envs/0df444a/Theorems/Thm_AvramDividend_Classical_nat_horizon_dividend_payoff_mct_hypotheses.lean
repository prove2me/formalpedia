-- Prove2me | Theorems.Thm_AvramDividend_Classical_nat_horizon_dividend_payoff_mct_hypotheses
-- name    : AvramDividend.Classical.nat_horizon_dividend_payoff_mct_hypotheses
-- status  : Open
-- author  : @WillR
-- created : 2026-10-07T06:30:47.225092+00:00
-- url     : https://prove2.me/theorems/b87f9765-815a-4ff6-b11b-9e5a802b6df8
-- title:
--   Measurability, monotonicity and convergence of integer-horizon dividend payoffs
-- statement:
--   For the pathwise discounted Stieltjes dividend payoff, truncation at deterministic integer horizons gives an a.e. measurable sequence, increasing almost surely in the horizon and converging almost surely to the full payoff up to ruin. These are exactly the hypotheses needed for the monotone-convergence step in Proposition 4(i).
-- source:
--   Formal measurability and pathwise exhaustion content of the monotone-convergence passage after equation (5.13) in Avram, Palmowski and Pistorius (2007), Proposition 4(i). The deterministic payment-time union is separated as paymentTimes_eq_iUnion_nat_horizons.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.nat_horizon_dividend_payoff_mct_hypotheses
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) :
    (∀ n : ℕ, AEMeasurable
      (fun ω => ∫⁻ t in
        paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) P) ∧
    (∀ᵐ ω ∂P, Monotone (fun n : ℕ =>
      ∫⁻ t in paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω))) ∧
    (∀ᵐ ω ∂P, Tendsto
      (fun n : ℕ =>
        ∫⁻ t in paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)),
          ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω))
      atTop
      (𝓝 (∫⁻ t in paymentTimes (ruinTime X x D ω),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)))) := by sorry
