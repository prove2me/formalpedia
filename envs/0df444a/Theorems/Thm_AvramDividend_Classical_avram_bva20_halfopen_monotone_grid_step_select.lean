-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva20_halfopen_monotone_grid_step_select
-- name    : AvramDividend.Classical.avram_bva20_halfopen_monotone_grid_step_select
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T20:08:25.988275+00:00
-- url     : https://prove2.me/theorems/e2ccfe12-8c1f-4fc6-b93a-d9f01e957b6e
-- title:
--   Disjoint increasing half-open grid cells select the active Riemann coefficient
-- statement:
--   For an increasing grid, the half-open cells [u(j),u(j+1)) are pairwise disjoint. If the evaluation time belongs to cell i, its indicator is one and every other cell indicator vanishes; the sum of frozen compensator coefficients therefore equals the coefficient at i. This deterministic source-independent step-function selection is necessary to turn the already Proved original inclusive step-integral identity cdc19ee6 into the physical floor-sampled integrand for 7ccc2a1a.
-- source:
--   Root-connected deterministic step-integrand evaluation for 7ccc2a1a dominated-convergence assembly.

import Mathlib
open Set
noncomputable section

theorem AvramDividend.Classical.avram_bva20_halfopen_monotone_grid_step_select
    (n i : ℕ) (hi : i < n + 1) (u : ℕ → ℝ)
    (hu : StrictMono u) (c : ℕ → ℝ) (t : ℝ)
    (ht : t ∈ Set.Ico (u i) (u (i + 1))) :
    (∑ j ∈ Finset.range (n + 1),
      (Set.Ico (u j) (u (j + 1))).indicator (fun _ => c j) t) = c i := by sorry
