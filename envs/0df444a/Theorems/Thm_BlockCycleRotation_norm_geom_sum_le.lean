-- Prove2me | Theorems.Thm_BlockCycleRotation_norm_geom_sum_le
-- name    : BlockCycleRotation.norm_geom_sum_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T09:51:24.750412+00:00
-- url     : https://prove2.me/theorems/610d036d-637a-44ef-bf7f-5f0a7343a4fa
-- title:
--   Observation 17, geometric sum
-- statement:
--   **Observation 17, geometric sum.** For `0 < |θ| ≤ π`, `‖∑_{B ≤ j < T} e(jθ)‖ ≤ π / |θ|`. This is the trivial bound: the sum telescopes to a quotient whose numerator has norm at most `2`, and the denominator is bounded below by Jordan's inequality.
--
--   In Blomer–Bux this is **Obs. 17**, “Obs. 17: geometric sum bound”. It is used in the proof of `norm_weighted_geom_sum_le`.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1 -- Obs. 17. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/ExpSum.lean#L126-L145

import Definitions.Def_BlockCycleRotation_ExpSum
import Mathlib

open BlockCycleRotation
open Real Finset

theorem BlockCycleRotation.norm_geom_sum_le {θ : ℝ} (h0 : θ ≠ 0) (h : |θ| ≤ π) (B T : ℕ) :
    ‖∑ j ∈ Finset.Ico B T, e θ ^ j‖ ≤ π / |θ| := by sorry
