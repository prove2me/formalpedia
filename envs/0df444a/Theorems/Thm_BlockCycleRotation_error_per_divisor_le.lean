-- Prove2me | Theorems.Thm_BlockCycleRotation_error_per_divisor_le
-- name    : BlockCycleRotation.error_per_divisor_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T09:58:25.865385+00:00
-- url     : https://prove2.me/theorems/1a3a7daf-6435-432b-922f-ec3e697a5a4e
-- title:
--   The per-divisor error `(n/d)^{3/2}·√d` is `n^{3/2}/d`, hence at most `n^{3/2}`
-- statement:
--   The per-divisor error `(n/d)^{3/2}·√d` is `n^{3/2}/d`, hence at most `n^{3/2}`.
--
--   In Blomer–Bux this is **Lemma 19**, “`d`-sum: errors `≤ d(n)·n^{3/2}`”.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1 -- Lemma 19. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/Constant.lean#L462-L477

import Mathlib

open Real Finset

theorem BlockCycleRotation.error_per_divisor_le {n d : ℕ} (hn : 0 < n) (hd : d ∈ n.divisors) :
    ((n / d : ℕ) : ℝ) ^ (3 / 2 : ℝ) * (d : ℝ) ^ ((1 : ℝ) / 2)
      ≤ (n : ℝ) ^ (3 / 2 : ℝ) := by sorry
