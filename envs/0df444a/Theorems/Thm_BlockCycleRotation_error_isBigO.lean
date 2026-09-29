-- Prove2me | Theorems.Thm_BlockCycleRotation_error_isBigO
-- name    : BlockCycleRotation.error_isBigO
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T09:57:01.348941+00:00
-- url     : https://prove2.me/theorems/0cbfe98f-92e4-476c-a566-47d302477553
-- title:
--   The aggregate error is $O(n^{3/2+\varepsilon})$
-- statement:
--   For every $\varepsilon>0$ there is $C_\varepsilon>0$ with
--   $$\tau(n)\left(\sqrt n + 1\right) 3n\,(1+\log n) \le C_\varepsilon\, n^{3/2+\varepsilon} \qquad (n \ge 1).$$
--
--   The three estimation layers combined. The divisor function and the logarithm are each $O(n^{\varepsilon})$, so the whole error is $O(n^{3/2+\varepsilon})$ — the bound Lemmas 18 and 19 establish for $G_2+G_3$.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1 -- Lemmas 16 and 18. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/TripleSum.lean#L1107-L1174

import Mathlib

open Real Finset

theorem BlockCycleRotation.error_isBigO {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 0 < n →
      (n.divisors.card : ℝ) * (((Nat.sqrt n : ℝ) + 1) * (3 * (n : ℝ) * (1 + Real.log n)))
        ≤ C * (n : ℝ) ^ (3 / 2 + ε) := by sorry
