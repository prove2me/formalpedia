-- Prove2me | Theorems.Thm_BlockCycleRotation_exists_card_divisors_le
-- name    : BlockCycleRotation.exists_card_divisors_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T09:53:17.996494+00:00
-- url     : https://prove2.me/theorems/c04fb3bd-4287-48aa-bbc9-5bb7e33858f1
-- title:
--   The divisor bound
-- statement:
--   **The divisor bound.** For every `ε > 0` there is a constant `C` with `d(n) ≤ C · n^ε` for all `n ≥ 1`. The primes dividing `n` are split at `p^ε = 2`. Above the cut each factor `k + 1 ≤ 2^k ≤ (p^ε)^k` costs nothing; below it — finitely many primes, all less than `2^(1/ε)` — each costs a constant `C₀`, and their number is bounded independently of `n`.
--
--   In Blomer–Bux this is **§4 (cited as standard)**, “Divisor bound `d(n) = O(nᵋ)`”. It is used in the proofs of `R_isBigO`, `error_isBigO`, `invquant`, `lemma17_isBigO`, and 3 further result(s).
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1 -- §4 (cited as standard). Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/DivisorBound.lean#L131-L203

import Mathlib

open Real Finset

theorem BlockCycleRotation.exists_card_divisors_le {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, n ≠ 0 → ((n.divisors.card : ℝ)) ≤ C * (n : ℝ) ^ ε := by sorry
