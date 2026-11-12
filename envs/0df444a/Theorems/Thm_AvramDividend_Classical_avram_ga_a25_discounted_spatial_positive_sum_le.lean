-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a25_discounted_spatial_positive_sum_le
-- name    : AvramDividend.Classical.avram_ga_a25_discounted_spatial_positive_sum_le
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T00:31:30.128008+00:00
-- url     : https://prove2.me/theorems/284bf1a4-f9c8-4ecb-89b0-9ac4eb490203
-- title:
--   Discounted clipped Gaussian finite spatial error positive-part sum majorant
-- statement:
--   For the exact discounted stopped uniform grid v(i) used by the original Gaussian spatial ledger, the positive part of a finite discounted sum of arbitrary signed cell errors is bounded by the discounted sum of their positive parts. No absolute error limit is assumed. This enables cellwise one-sided bounds on gledger179 Taylor residuals.
-- source:
--   Follows from positivity of exp weights and finite sum monotonicity. A source-specific deterministic bridge in the gledger175 and gledger179 original Gaussian route.

import Mathlib
open MeasureTheory
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_a25_discounted_spatial_positive_sum_le
    (m n : ℕ) (ρ : ℝ≥0) (q : ℝ) (R : ℕ → ℝ) :
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let v : ℕ → ℝ≥0 := fun i => min ((i : ℝ≥0) * Δ) ρ
    let E : ℕ → ℝ := fun i => Real.exp (-(q * (v i : ℝ)))
    max (∑ i ∈ Finset.range (m + 1), E i * R i) 0 ≤
      ∑ i ∈ Finset.range (m + 1), E i * max (R i) 0 := by sorry
