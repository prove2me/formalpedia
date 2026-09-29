-- Prove2me | Theorems.Thm_BlockCycleRotation_sum_inv_sq_tail_le
-- name    : BlockCycleRotation.sum_inv_sq_tail_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T09:58:00.87322+00:00
-- url     : https://prove2.me/theorems/836b6b69-678c-495a-b29c-bfa516e4297c
-- title:
--   For any finite set of integers beyond `N`, the sum of `1/a²` is at most `1/N`
-- statement:
--   For any finite set of integers beyond `N`, the sum of `1/a²` is at most `1/N`.
--
--   In Blomer–Bux this is **Lemma 19**, “Tail bound `∑_{a>N} 1/a² ≤ 1/N`”. It is used in the proofs of `cConst_le_partial_add`, `cConst_le_partial_add_sharp`, `tsum_gTerm_le_partial`, `tsum_tail_inv_sq`.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1 -- Lemma 19. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/Constant.lean#L183-L199

import Mathlib

open Real Finset

theorem BlockCycleRotation.sum_inv_sq_tail_le {N : ℕ} (hN : 0 < N) (s : Finset ℕ) (hs : ∀ a ∈ s, N < a) :
    ∑ a ∈ s, 1 / ((a : ℝ) ^ 2) ≤ 1 / (N : ℝ) := by sorry
