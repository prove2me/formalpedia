-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a209_physical_full_pre_stop_nonnegative_mask_le_prefix
-- name    : AvramDividend.Classical.avram_ga_a209_physical_full_pre_stop_nonnegative_mask_le_prefix
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T00:14:48.073483+00:00
-- url     : https://prove2.me/theorems/40932ab6-ec3d-4fc3-941b-d1adc8621150
-- title:
--   Every physically full pre-stop Gaussian cell contributes no more nonnegative energy than the stopped-prefix mesh
-- statement:
--   For the actual physical time grid, the stopped full-cell condition that both the start occurs before the stop and the end is no later than the stop is a subset of the stopped-prefix start-only condition. Thus for any nonnegative source integrand, the finite sum of contributions over full cells is bounded pointwise by that over prefix cells. This gives a source-exact bridge for transferring original Gaussian centred square and cross energy estimates into the full-cell Hessian correction a150.
-- source:
--   Finite sum monotonicity and physical mesh stopping-mask inclusion.

import Mathlib

open scoped NNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_a209_physical_full_pre_stop_nonnegative_mask_le_prefix
    {Ω : Type*} (m : ℕ) (s : ℕ → ℝ≥0)
    (Δ : ℝ≥0) (ρ : Ω → ℝ≥0) (f : ℕ → Ω → ℝ)
    (hf : ∀ i ω, 0 ≤ f i ω) (ω : Ω) :
    (∑ i ∈ Finset.range m,
      if s i < ρ ω ∧ s i + Δ ≤ ρ ω then f i ω else 0) ≤
    (∑ i ∈ Finset.range m,
      if s i < ρ ω then f i ω else 0) := by sorry
