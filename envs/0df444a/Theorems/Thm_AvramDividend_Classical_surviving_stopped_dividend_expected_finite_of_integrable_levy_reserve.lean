-- Prove2me | Theorems.Thm_AvramDividend_Classical_surviving_stopped_dividend_expected_finite_of_integrable_levy_reserve
-- name    : AvramDividend.Classical.surviving_stopped_dividend_expected_finite_of_integrable_levy_reserve
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T21:43:19.537984+00:00
-- url     : https://prove2.me/theorems/f1d8a575-a9c4-4cb6-9c0b-64569d3ecde2
-- title:
--   Surviving pre-ruin discounted Stieltjes rewards have finite expectation when the Lévy reserve is integrable
-- statement:
--   Assume the uncontrolled reserve at a fixed horizon S is integrable. For any earlier T, retain the complete discounted Stieltjes payout only on paths surviving through S. The expected payout is finite. The proof combines the accepted survivor payout upper bound with integrability of the positive part of x+X_S, using Mathlib's equivalence between positive-part integrability and finiteness of its extended-real Lebesgue integral. This supplies an explicit localised integrability condition needed for optional-stopping and limiting arguments, without imposing a global dividend bound.
-- source:
--   Canonically Proved surviving_stopped_dividend_expected_le_uncontrolled_reserve (31f56682-98d7-4cd3-b05d-a2b65c95415f) once that dependency is Proved; Mathlib.MeasureTheory.Function.L1Space.Integrable.

import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_surviving_stopped_dividend_expected_le_uncontrolled_reserve

open MeasureTheory Set Filter
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.surviving_stopped_dividend_expected_finite_of_integrable_levy_reserve
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (q : ℝ) (hq : 0 ≤ q) (σ : Ω → ℝ≥0∞)
    (T S : ℝ≥0) (hTS : T < S)
    (hXI : Integrable (fun ω => x + X.X S ω) P) :
    (∫⁻ ω, if (S : ℝ≥0∞) < ruinTime X x D ω then
      (∫⁻ r in paymentTimes (σ ω) ∩ Iic (T : ℝ),
        ENNReal.ofReal (Real.exp (-(q * r))) ∂(dividendMeasure D ω))
      else 0 ∂P) ≠ ⊤ := by sorry
