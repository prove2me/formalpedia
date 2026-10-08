-- Prove2me | Theorems.Thm_CollatzFrontier_terminal_power_contraction
-- name    : CollatzFrontier.terminal_power_contraction
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-10-04T17:25:08.362177+00:00
-- url     : https://prove2.me/theorems/7dd4394e-e27e-4d04-aca0-b524d5d496cc
-- title:
--   A positive affine intercept forces power-of-two contraction from mere nonincrease
-- statement:
--   Let $(b_i)_{i\le k}$ and $(a_i)_{i<k}$ be natural-number sequences satisfying the affine recursion
--
--   $$3\,b_i + 1 = 2^{a_i}\,b_{i+1} \qquad (i<k),$$
--
--   and let a final row close the chain with exponent $e$ and value $B$,
--
--   $$3\,b_k + 1 = 2^{e}\,B.$$
--
--   Write $S=\sum_{i<k} a_i$. If the chain is merely nonincreasing at its two ends, $B \le b_0$, then it is already a strict power-of-two contraction:
--
--   $$3^{k+1} < 2^{S+e}.$$
--
--   **Role.** This isolates the purely arithmetic content of the 'power-of-two contraction' side condition that appears when deriving residue-class descent for the Syracuse map $T(n)=(3n+1)/2^{v_2(3n+1)}$ from a finite chain of exact steps: contraction is not an extra assumption to verify, it is a theorem about any chain whose representative values merely fail to increase.
--
--   **Formalization note.** The statement is pure $\mathbb N$-arithmetic; it does not mention the Syracuse map, parity, or any project-specific definition, and needs none.
-- source:
--   collatz-frontier (private repo), commit 4d656b9c9c5815305bd391f206c9d3e9587dd395, lean/CollatzFrontier/AffineDrift.lean, declaration terminal_power_contraction. Original result of this contribution (elementary, used internally to remove a redundant contraction hypothesis from a uniform-descent interface for the Syracuse map; no claim of prior-literature novelty is made).

import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

namespace CollatzFrontier

theorem terminal_power_contraction (a b : ℕ → ℕ) (k e B : ℕ)
    (hstep : ∀ i < k, 3 * b i + 1 = 2 ^ (a i) * b (i + 1))
    (hfinal : 3 * b k + 1 = 2 ^ e * B)
    (hdesc : B ≤ b 0) :
    3 ^ (k + 1) < 2 ^ ((∑ i ∈ Finset.range k, a i) + e) := by sorry

end CollatzFrontier
