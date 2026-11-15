-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a429_monotone_L1_uniform_budget_integrable_envelope
-- name    : AvramDividend.Classical.avram_ga_a429_monotone_L1_uniform_budget_integrable_envelope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T23:53:24.075367+00:00
-- url     : https://prove2.me/theorems/760e1446-75a4-4693-b9dd-93dae65419cf
-- title:
--   A uniformly L1 bounded nonnegative increasing sequence has an integrable common envelope
-- statement:
--   If a pointwise nondecreasing sequence of measurable nonnegative integrable real random variables has uniformly bounded expectations, then an integrable random variable dominates the whole sequence almost surely.
-- source:
--   Monotone convergence of the extended nonnegative integral, conversion of finite ENNReal almost-everywhere limits to integrable real values.

import Mathlib
open MeasureTheory Set Filter
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_a429_monotone_L1_uniform_budget_integrable_envelope
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (f : ℕ → Ω → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hint : ∀ k, Integrable (f k) P)
    (hmeas : ∀ k, Measurable (f k))
    (hnonneg : ∀ k ω, 0 ≤ f k ω)
    (hmono : ∀ ω, Monotone (fun k => f k ω))
    (hbudget : ∀ k, (∫ ω, f k ω ∂P) ≤ K) :
    ∃ S : Ω → ℝ, Integrable S P ∧
      ∀ᵐ ω ∂P, 0 ≤ S ω ∧ ∀ k, f k ω ≤ S ω := by sorry
