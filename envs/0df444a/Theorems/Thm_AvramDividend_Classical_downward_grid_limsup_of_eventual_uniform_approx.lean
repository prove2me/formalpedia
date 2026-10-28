-- Prove2me | Theorems.Thm_AvramDividend_Classical_downward_grid_limsup_of_eventual_uniform_approx
-- name    : AvramDividend.Classical.downward_grid_limsup_of_eventual_uniform_approx
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T20:31:33.670427+00:00
-- url     : https://prove2.me/theorems/fd58688a-8c36-4760-a4f3-e087eda6a320
-- title:
--   Infinitely recurrent negative grid increments survive eventual uniform path approximation with a twice-error threshold
-- statement:
--   Let g_n be a sequence of paths, and f a limiting path. Suppose from some index onward |f(t)-g_n(t)|≤epsilon uniformly in all times t. Suppose arbitrarily fine finite grids contain a g_n downward decrement exceeding a+2epsilon. Then arbitrarily fine grids also contain an f decrement exceeding a. The proof uses the same grid index n, both endpoint uniform-error estimates, and a cofinal maximum of the requested index and the uniform-approximation starting index. This is the deterministic transfer needed to pass canonical Poisson finite-annulus grid events through a uniform-on-compacts compensated small-jump limit before using equality of law.
-- source:
--   LeanLevy/RandomMeasure/LevyJumpPath.lean yields a.e. uniform-on-compacts convergence of truncation paths; accepted measurable downward_grid_limsup_event_measurable [3588ab51-c596-4dd9-9411-29c3c710979c].

import Mathlib.Data.NNReal.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Data.Finset.Basic

open scoped BigOperators
open scoped NNReal

theorem AvramDividend.Classical.downward_grid_limsup_of_eventual_uniform_approx
    (grid : ℕ → Finset (ℝ≥0 × ℝ≥0))
    (f : ℝ≥0 → ℝ) (g : ℕ → ℝ≥0 → ℝ) (a ε : ℝ)
    (hclose : ∃ N₀ : ℕ, ∀ n ≥ N₀, ∀ t : ℝ≥0, |f t - g n t| ≤ ε)
    (happroxdrops : ∀ N : ℕ, ∃ n ≥ N, ∃ ij ∈ grid n,
      g n ij.2 - g n ij.1 < -(a + 2 * ε)) :
    ∀ N : ℕ, ∃ n ≥ N, ∃ ij ∈ grid n,
      f ij.2 - f ij.1 < -a := by sorry
