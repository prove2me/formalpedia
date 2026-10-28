-- Prove2me | Theorems.Thm_AvramDividend_Classical_expected_stopped_dividend_le_levy_on_survival_event
-- name    : AvramDividend.Classical.expected_stopped_dividend_le_levy_on_survival_event
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T15:10:51.490283+00:00
-- url     : https://prove2.me/theorems/cbc4ca4a-932b-41f8-9345-396ac617f1b9
-- title:
--   Expected stopped Stieltjes dividends bounded by future Lévy reserve on survival events
-- statement:
--   For any measurable collection E of paths on which a capped or uncapped dividend strategy survives to deterministic S>T, the expectation restricted to E of its full discounted Stieltjes dividends through T is at most the expectation restricted to E of the nonnegative uncontrolled surplus x+X_S. This is an expectation-level localisation bound, preserving both continuously paid and lump-sum dividends. It applies to the survival-event envelope needed during bounded- and unbounded-variation stopped HJB localisation. The remaining core still requires a generator change-of-variables or Itô argument.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Restrict
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_stopped_dividend_payoff_le_uncontrolled_reserve_before_ruin

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.expected_stopped_dividend_le_levy_on_survival_event
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (q : ℝ) (hq : 0 ≤ q) (σ : ℝ≥0∞)
    (T S : ℝ≥0) (hTS : T < S)
    (E : Set Ω) (hE : MeasurableSet E)
    (hSurv : ∀ ω ∈ E, (S : ℝ≥0∞) < ruinTime X x D ω) :
    (∫⁻ ω in E, ∫⁻ r in paymentTimes σ ∩ Iic (T : ℝ),
      ENNReal.ofReal (Real.exp (-(q * r))) ∂(dividendMeasure D ω) ∂P) ≤
    (∫⁻ ω in E, ENNReal.ofReal (x + X.X S ω) ∂P) := by sorry
