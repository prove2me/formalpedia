-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_eventually_small_nonjump_source_grid_cells
-- name    : AvramDividend.Classical.avram_p2_a_zero_rate_eventually_small_nonjump_source_grid_cells
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T19:41:34.123211+00:00
-- url     : https://prove2.me/theorems/84fdbc0a-265f-4bb1-ba87-efa4a145ddce
-- title:
--   Uniformly fine original source mesh cells avoiding genuine large jumps have uniformly small increments
-- statement:
--   For a càdlàg original path on [0,T], if finite F contains all jumps of magnitude at least ρ>0 and a triangular family of shrinking cells avoids F, prove that eventually every cell in the row has increment magnitude less than ρ. This is a full-grid no-spurious-large-cell uniform bound derived from the proved frequent-bad-cell contradiction. No expected jump rate or compensator premise.

import Mathlib
open Set Filter Topology
open scoped NNReal

theorem AvramDividend.Classical.avram_p2_a_zero_rate_eventually_small_nonjump_source_grid_cells
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
       ρ ≤ |Y t - Function.leftLim Y t| → t ∈ F)
    (havoid : ∀ n i, ∀ t ∈ F, ¬ (a n i < t ∧ t ≤ b n i)) :
    ∀ᶠ n in (atTop : Filter ℕ),
      ∀ i, |Y (b n i) - Y (a n i)| < ρ := by sorry
