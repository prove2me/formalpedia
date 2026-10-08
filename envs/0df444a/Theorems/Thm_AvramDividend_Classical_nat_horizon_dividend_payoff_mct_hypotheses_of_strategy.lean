-- Prove2me | Theorems.Thm_AvramDividend_Classical_nat_horizon_dividend_payoff_mct_hypotheses_of_strategy
-- name    : AvramDividend.Classical.nat_horizon_dividend_payoff_mct_hypotheses_of_strategy
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T06:35:56.614981+00:00
-- url     : https://prove2.me/theorems/126fb142-bab2-4bcb-adda-9f448b6cc072
-- title:
--   MCT hypotheses for integer-horizon dividend payoffs of a dividend strategy
-- statement:
--   For an actual dividend strategy, deterministic integer-horizon discounted Stieltjes payoffs are a.e. measurable, increase almost surely and converge almost surely to the full payoff up to ruin. This is the correctly strategy-scoped hypothesis bundle for monotone convergence.
-- source:
--   Formal version of the monotone-convergence prerequisites after equation (5.13) in Avram, Palmowski and Pistorius (2007), Proposition 4(i). The dividend-strategy assumption supplies adaptedness and path regularity needed for random-payoff measurability.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.nat_horizon_dividend_payoff_mct_hypotheses_of_strategy
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D) :
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
