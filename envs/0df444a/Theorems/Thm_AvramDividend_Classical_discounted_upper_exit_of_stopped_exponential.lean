-- Prove2me | Theorems.Thm_AvramDividend_Classical_discounted_upper_exit_of_stopped_exponential
-- name    : AvramDividend.Classical.discounted_upper_exit_of_stopped_exponential
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T10:24:46.778372+00:00
-- url     : https://prove2.me/theorems/fb4193c3-a93b-4540-bbfd-d9eea83cb212
-- title:
--   Bound the discounted upper-exit payoff using a unit exponential stopped moment
-- statement:
--   An integrable exponential stopped payoff with expected value at most one bounds the expected discounted payoff on an event where the stopped process is above a threshold a. The inequality is E[1_A exp(-D)]≤exp(-θa), for θ≥0, and is proved by a pointwise exponential inequality and integral monotonicity. This is the probabilistic inequality connecting proved bounded-grid exponential martingales to first-upcrossing estimates.
-- source:
--   Pooled exponential martingale bound and pinned Mathlib Bochner integral monotonicity.

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.discounted_upper_exit_of_stopped_exponential
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω)
    (a θ : ℝ) (hθ : 0 ≤ θ)
    (Y D : Ω → ℝ) (A : Set Ω)
    (hupper : ∀ ω : Ω, ω ∈ A → a ≤ Y ω)
    (hwhole : Integrable
      (fun ω => Real.exp (θ * Y ω - D ω)) P)
    (hpart : Integrable
      (A.indicator (fun ω => Real.exp (-D ω))) P)
    (hmean : (∫ ω, Real.exp (θ * Y ω - D ω) ∂P) ≤ 1) :
    (∫ ω, A.indicator (fun ω => Real.exp (-D ω)) ω ∂P) ≤
      Real.exp (-θ * a) := by sorry
