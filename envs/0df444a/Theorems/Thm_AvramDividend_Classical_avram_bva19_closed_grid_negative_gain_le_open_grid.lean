-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva19_closed_grid_negative_gain_le_open_grid
-- name    : AvramDividend.Classical.avram_bva19_closed_grid_negative_gain_le_open_grid
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T17:43:25.323889+00:00
-- url     : https://prove2.me/theorems/8c5e233d-54d9-4980-a052-364bc90bedff
-- title:
--   Original uniform-grid closed-cap negative gain is dominated by the strict interior sum
-- statement:
--   A purely finite-grid source lemma: when the compensated negative-mark gain is nonpositive throughout the closed reserve cap and the source time grid is monotone, dropping the zero-reserve and cap-boundary cells makes its sum larger. This is the exact algebraic one-sided bridge from the original compensator's closed reserve mask to the physical grid's strict interior mask, including index zero, the ruin-clock threshold and nonnegative mesh widths.
-- source:
--   Necessary deterministic signed-grid comparison for original positive-intensity later-ruin compensated Riemann quadrature efbae9c3; original negative gain sign is available from already Proved ff6949ca.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bva19_closed_grid_negative_gain_le_open_grid
    (C : ℝ≥0∞) (u : ℕ → ℕ → ℝ≥0)
    (hmono : ∀ n i, i < n + 1 → u n i ≤ u n (i + 1))
    (τ : ℝ≥0∞) (U : ℝ≥0 → ℝ) (q : ℝ)
    (ψ : ℝ → ℝ)
    (hψ : ∀ a : ℝ, 0 ≤ a → ENNReal.ofReal a ≤ C → ψ a ≤ 0)
    (n : ℕ) :
    (∑ i ∈ Finset.range (n + 1),
      if (u n i : ℝ≥0∞) < τ ∧
          0 ≤ U (u n i) ∧ ENNReal.ofReal (U (u n i)) ≤ C then
        Real.exp (-(q * (u n i : ℝ))) * ψ (U (u n i)) *
          ((u n (i + 1) : ℝ) - (u n i : ℝ))
      else 0) ≤
    (∑ i ∈ Finset.range (n + 1),
      if (u n i : ℝ≥0∞) < τ ∧
          0 < U (u n i) ∧ ENNReal.ofReal (U (u n i)) < C then
        Real.exp (-(q * (u n i : ℝ))) * ψ (U (u n i)) *
          ((u n (i + 1) : ℝ) - (u n i : ℝ))
      else 0) := by sorry
