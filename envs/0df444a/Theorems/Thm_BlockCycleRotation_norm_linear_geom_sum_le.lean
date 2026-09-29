-- Prove2me | Theorems.Thm_BlockCycleRotation_norm_linear_geom_sum_le
-- name    : BlockCycleRotation.norm_linear_geom_sum_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T09:52:56.079959+00:00
-- url     : https://prove2.me/theorems/cbe48777-cca1-4279-803f-21d563fd9242
-- title:
--   The inner sum
-- statement:
--   **The inner sum.** A linear function twisted by a character, bounded by the chord length.
--
--   This is an auxiliary lemma of the formalization rather than a result stated in the paper.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/LinearSums.lean#L37-L57

import Definitions.Def_BlockCycleRotation_ExpSum
import Mathlib

open BlockCycleRotation
open Real Finset

theorem BlockCycleRotation.norm_linear_geom_sum_le {θ : ℝ} (hne : e θ ≠ 1) (A B : ℂ) (T : ℕ) :
    ‖∑ b ∈ Finset.Ico 1 T, (A + B * b) * e θ ^ b‖
      ≤ (‖A‖ + ‖B‖ * (T - 1 : ℕ)) * (2 / ‖e θ - 1‖) := by sorry
