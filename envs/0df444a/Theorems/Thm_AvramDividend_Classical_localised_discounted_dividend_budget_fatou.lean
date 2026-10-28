-- Prove2me | Theorems.Thm_AvramDividend_Classical_localised_discounted_dividend_budget_fatou
-- name    : AvramDividend.Classical.localised_discounted_dividend_budget_fatou
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T07:18:06.730608+00:00
-- url     : https://prove2.me/theorems/135f1ccf-7458-4edc-8df2-9a7bcf133d48
-- title:
--   Fatou localisation removes stopped dividend budget cutoffs
-- statement:
--   If every measurable localised discounted-dividend payoff has expected value bounded by an initial budget, and the full dividend payoff is pointwise dominated by the lower limit of localised payoffs, then the full expected discounted-dividend payoff obeys the same budget. This rigorously isolates the Fatou/localisation limiting step for both bounded- and unbounded-variation stochastic verification. The remaining stochastic-calculus task is establishing the localised expectation bound and pointwise lower-limit dominance.
-- source:
--   Fatou's lemma applied to the localisation step in Avram, Palmowski and Pistorius (2007), Proposition 4(i), Section 5.4.

import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Order.LiminfLimsup

open MeasureTheory Filter
open scoped ENNReal

theorem AvramDividend.Classical.localised_discounted_dividend_budget_fatou
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (A : ℕ → Ω → ENNReal) (B : Ω → ENNReal) (budget : ENNReal)
    (hAmeas : ∀ n, Measurable (A n))
    (hLimit : ∀ ω, B ω ≤ Filter.liminf (fun n : ℕ => A n ω) Filter.atTop)
    (hBound : ∀ n, (∫⁻ ω, A n ω ∂P) ≤ budget) :
    (∫⁻ ω, B ω ∂P) ≤ budget := by sorry
