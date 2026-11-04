-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_uniform_large_cells_cross_finite_true_jumps
-- name    : AvramDividend.Classical.avram_p2_a_zero_rate_uniform_large_cells_cross_finite_true_jumps
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T19:48:37.969736+00:00
-- url     : https://prove2.me/theorems/34988989-4932-442c-b447-e74dccd17dbe
-- title:
--   Eventually every significant source mesh cell crosses a genuine jump in finite F
-- statement:
--   Full-grid reverse jump matching for the genuine original càdlàg path: if a shrinking grid row includes a cell increment of magnitude at least ρ, then at sufficiently fine resolution that cell must straddle one of finitely many real path jump times of magnitude at least ρ. Contradiction chooses a cofinal bad-cell sequence and invokes the source-backed finite-jump exclusion helper. No compensator assumption.

import Mathlib
open Set Filter Topology
open scoped NNReal

theorem AvramDividend.Classical.avram_p2_a_zero_rate_uniform_large_cells_cross_finite_true_jumps
    (Y : ℝ≥0 → ℝ) (T : ℝ≥0)
    (a b : ℕ → ℕ → ℝ≥0) (w : ℕ → ℝ≥0)
    (haT : ∀ n i, a n i ≤ T)
    (hab : ∀ n i, a n i ≤ b n i)
    (hbw : ∀ n i, b n i ≤ a n i + w n)
    (hw : Tendsto w atTop (𝓝 (0 : ℝ≥0)))
    (hL : ∀ t : ℝ≥0,
      Tendsto Y (𝓝[<] t) (𝓝 (Function.leftLim Y t)))
    (hR : ∀ t : ℝ≥0, ContinuousWithinAt Y (Ici t) t)
    (ρ : ℝ) (hρ : 0 < ρ)
    (F : Finset ℝ≥0)
    (hF : ∀ t ∈ Icc (0 : ℝ≥0) T,
      ρ ≤ |Y t - Function.leftLim Y t| → t ∈ F) :
    ∀ᶠ n in (atTop : Filter ℕ), ∀ i,
      ρ ≤ |Y (b n i) - Y (a n i)| →
      ∃ t ∈ F, a n i < t ∧ t ≤ b n i  := by sorry
