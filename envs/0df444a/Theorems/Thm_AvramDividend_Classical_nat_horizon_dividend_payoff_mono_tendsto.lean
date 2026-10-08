-- Prove2me | Theorems.Thm_AvramDividend_Classical_nat_horizon_dividend_payoff_mono_tendsto
-- name    : AvramDividend.Classical.nat_horizon_dividend_payoff_mono_tendsto
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T06:35:33.805926+00:00
-- url     : https://prove2.me/theorems/731b26be-fedb-4366-b551-27809ff5c156
-- title:
--   Pathwise monotonicity and convergence of deterministic-horizon dividend payoffs
-- statement:
--   For every sample path, the discounted Stieltjes dividend payoff accumulated before ruin and before integer horizon n is monotone in n and converges to the full pathwise payoff up to ruin. This is the deterministic pathwise half of the monotone-convergence step in Proposition 4(i).
-- source:
--   Pathwise exhaustion content of the monotone-convergence passage after equation (5.13), using paymentTimes_eq_iUnion_nat_horizons and monotonicity of positive Stieltjes integrals.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.nat_horizon_dividend_payoff_mono_tendsto
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) :
    (∀ ω, Monotone (fun n : ℕ =>
      ∫⁻ t in paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω))) ∧
    (∀ ω, Tendsto
      (fun n : ℕ =>
        ∫⁻ t in paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)),
          ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω))
      atTop
      (𝓝 (∫⁻ t in paymentTimes (ruinTime X x D ω),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)))) := by sorry
