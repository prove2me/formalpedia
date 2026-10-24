-- Prove2me | Theorems.Thm_AvramDividend_Classical_surviving_stopped_dividend_expected_finite_at_integer_horizon
-- name    : AvramDividend.Classical.surviving_stopped_dividend_expected_finite_at_integer_horizon
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T22:04:42.394418+00:00
-- url     : https://prove2.me/theorems/2ae6ddb2-01e7-49c7-96d9-8dc0df345662
-- title:
--   Under the Lévy standing assumptions, surviving discounted Stieltjes dividends have finite expectation at integer localisation horizons
-- statement:
--   Under the Avram classical standing assumptions, fix a positive integer horizon n and an earlier time T. The discounted Stieltjes dividend payout through T, restricted to paths that have not been ruined at n, has finite expectation. The standing assumptions give integrability at unit time; stationarity propagates integrability to n, and the proved surviving-payout domination bounds the reward by the integrable reserve x+X_n. This supplies a concrete surviving-path localisation estimate for the BV and UV stopped verification proofs.
-- source:
--   Canonically Proved surviving_stopped_dividend_expected_finite_of_integrable_levy_reserve (f1d8a575-a9c4-4cb6-9c0b-64569d3ecde2) and levy_nat_horizon_integrable_of_standing upon acceptance, from the Avram classical Lean formalisation.

import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_levy_nat_horizon_integrable_of_standing
import Theorems.Thm_AvramDividend_Classical_surviving_stopped_dividend_expected_finite_of_integrable_levy_reserve

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.surviving_stopped_dividend_expected_finite_at_integer_horizon
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (q : ℝ) (hq : 0 ≤ q) (σ : Ω → ℝ≥0∞)
    (T : ℝ≥0) (n : ℕ) (hT : T < (n : ℝ≥0)) :
    (∫⁻ ω, if ((n : ℝ≥0) : ℝ≥0∞) < ruinTime X x D ω then
      (∫⁻ r in paymentTimes (σ ω) ∩ Iic (T : ℝ),
        ENNReal.ofReal (Real.exp (-(q * r))) ∂(dividendMeasure D ω))
      else 0 ∂P) ≠ ⊤ := by sorry
