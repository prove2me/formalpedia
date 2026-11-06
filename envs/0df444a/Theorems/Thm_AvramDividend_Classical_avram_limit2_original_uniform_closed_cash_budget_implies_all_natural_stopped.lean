-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_limit2_original_uniform_closed_cash_budget_implies_all_natural_stopped
-- name    : AvramDividend.Classical.avram_limit2_original_uniform_closed_cash_budget_implies_all_natural_stopped
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T17:43:27.494215+00:00
-- url     : https://prove2.me/theorems/5893b0c6-d714-47cc-a6f8-a969bc955cd8
-- title:
--   Exact original uniform closed-horizon Stieltjes cash budgets imply all natural stopped cash budgets including time zero
-- statement:
--   A uniform original nonnegative discounted Stieltjes cash estimate over paymentTimes(ruinTime) intersection Iic T, for all real T≥0, entails the same estimate on paymentTimes(min(ruinTime,n)) for every natural n including 0. The bridge applies already Proved/public original real stopped cash monotonicity 4eb76074 at T=n, uses exact casting ENNReal.ofReal(n:ℝ)=(n:ENNReal), and transitivity with the supplied closed-horizon budget. It is independent of canonical Open targets 6c39765b, e4317583, 61bbf167; once the combined truncated HJB estimate is Proved, this adapter formally supplies both BV/UBV natural-horizon sources without extra terminal vanishing assumptions. Source models and original dividendMeasure are unchanged.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_limit2_original_real_stopped_cash_le_closed_horizon_cash
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_limit2_original_uniform_closed_cash_budget_implies_all_natural_stopped
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (B : ℝ≥0∞)
    (hClosed : ∀ (T : ℝ) (hT : 0 ≤ T),
      (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Set.Iic T,
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω) ∂P) ≤ B) :
    ∀ n : ℕ,
      (∫⁻ ω, ∫⁻ t in paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω) ∂P) ≤ B := by sorry
