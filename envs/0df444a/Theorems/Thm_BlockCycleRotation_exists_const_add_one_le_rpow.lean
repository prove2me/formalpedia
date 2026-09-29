-- Prove2me | Theorems.Thm_BlockCycleRotation_exists_const_add_one_le_rpow
-- name    : BlockCycleRotation.exists_const_add_one_le_rpow
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T09:53:30.798459+00:00
-- url     : https://prove2.me/theorems/77916550-bb50-485a-95f3-b49524ae8499
-- title:
--   Small primes cost a constant
-- statement:
--   **Small primes cost a constant.** For `p ≥ 2` and `ε > 0`, `k + 1` is at most `C · (p^k)^ε` with `C` depending only on `ε`.
--
--   This is an auxiliary lemma of the formalization rather than a result stated in the paper. It is used in the proof of `exists_card_divisors_le`.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/DivisorBound.lean#L110-L127

import Mathlib

open Real Finset

theorem BlockCycleRotation.exists_const_add_one_le_rpow {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ p : ℕ, 2 ≤ p → ∀ k : ℕ,
      ((k : ℝ) + 1) ≤ C * (((p ^ k : ℕ) : ℝ)) ^ ε := by sorry
