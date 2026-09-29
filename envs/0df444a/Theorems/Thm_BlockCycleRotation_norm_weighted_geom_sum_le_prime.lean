-- Prove2me | Theorems.Thm_BlockCycleRotation_norm_weighted_geom_sum_le_prime
-- name    : BlockCycleRotation.norm_weighted_geom_sum_le_prime
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T09:51:20.492367+00:00
-- url     : https://prove2.me/theorems/64f3fe16-c2f2-4abe-a6b3-2ecf78ff6393
-- title:
--   The weighted sum bound in terms of the chord length, with no restriction on `θ`
-- statement:
--   The weighted sum bound in terms of the chord length, with no restriction on `θ`. Proved by the paper's double-counting argument: write `j` as the number of `B` with `1 ≤ B ≤ j`, swap the order of summation, and apply the geometric bound to each inner sum.
--
--   This is an auxiliary lemma of the formalization rather than a result stated in the paper. It is used in the proof of `norm_linear_geom_sum_le`.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/ExpSum.lean#L147-L165

import Definitions.Def_BlockCycleRotation_ExpSum
import Mathlib

open BlockCycleRotation
open Real Finset

theorem BlockCycleRotation.norm_weighted_geom_sum_le_prime {θ : ℝ} (hne : e θ ≠ 1) (T : ℕ) :
    ‖∑ j ∈ Finset.Ico 1 T, (j : ℂ) * e θ ^ j‖ ≤ (T - 1 : ℕ) * (2 / ‖e θ - 1‖) := by sorry
