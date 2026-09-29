-- Prove2me | Theorems.Thm_BlockCycleRotation_exists_const_add_one_le
-- name    : BlockCycleRotation.exists_const_add_one_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T09:53:08.36502+00:00
-- url     : https://prove2.me/theorems/f0adaf2b-6d67-433f-94c0-a2ed2fd05cad
-- title:
--   `k + 1` is `O(t^k)` for any `t > 1`, with an explicit constant
-- statement:
--   **`k + 1` is `O(t^k)` for any `t > 1`, with an explicit constant.** Taking `s = t - 1`, Bernoulli gives `t^k ≥ 1 + k·s`, and `max 1 (2/s)` works: for `k ≥ 1` we have `k + 1 ≤ 2k ≤ (2/s)·(k·s)`.
--
--   This is an auxiliary lemma of the formalization rather than a result stated in the paper. It is used in the proof of `exists_const_add_one_le_rpow`.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/DivisorBound.lean#L58-L87

import Mathlib

open Real Finset

theorem BlockCycleRotation.exists_const_add_one_le {t : ℝ} (ht : 1 < t) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ k : ℕ, (k : ℝ) + 1 ≤ C * t ^ k := by sorry
