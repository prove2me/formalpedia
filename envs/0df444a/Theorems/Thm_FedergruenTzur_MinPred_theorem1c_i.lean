-- Prove2me | Theorems.Thm_FedergruenTzur_MinPred_theorem1c_i
-- name    : FedergruenTzur.MinPred.theorem1c_i
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T12:12:43.619411+00:00
-- url     : https://prove2.me/theorems/3b9e431f-085d-4990-a63e-1f430fd8d7df
-- title:
--   THEOREM 1(c)(i): if g(2) ≤ D(j) then i_1 may be eliminated, (S∖{i_1}) ⊇ Ω(j)
-- statement:
--   In the dynamic lot size model with costs given by the recursion (2), fix $j \ge 1$ and let $S = \{i_1, \dots, i_r\}$, $r \ge 2$, with $\Omega(j) \subseteq S \subseteq \{1, \dots, j\}$ be ranked in nonascending order of $\tilde C$-values, ties in ascending order of period index, with critical values $g(1) = D(j)$ and $g(l) = G(i_l, i_{l-1})$. If $g(2) \le D(j)$, then $i_1$ may be eliminated from the collection of optimal predecessors:
--   $$
--   S \setminus \{i_1\} \supseteq \Omega(j).
--   $$
--
--   Together with parts (ii) and (iii), this gives the elimination rules by which the forward algorithm shrinks a superset of $\Omega(j)$ to $\Omega(j)$ itself.
--
--   **Formalization Note.** 0-based in Lean: $g(2)$ is `gval j L 1` and $i_1$ is `L.getD 0 0`. $\Omega(j)$ is taken in the open-interval reading of the definition item `Omega`; under the literal reading of the page this part fails when lines tie exactly at $D(j)$.
-- source:
--   Federgruen and Tzur, A Simple Forward Algorithm to Solve General Dynamic Lot Sizing Models with n Periods in O(n log n) or O(n) Time, Management Science 37(8), 1991, p. 915, THEOREM 1(c)(i)

import Mathlib
import Definitions.Def_FedergruenTzur_MinPred_Omega
import Definitions.Def_FedergruenTzur_MinPred_RankedList

namespace FedergruenTzur.MinPred

open LotSizing

/-- THEOREM 1(c)(i), p. 915: if `g(2) ≤ D(j)` then `i_1` may be eliminated, i.e.
`S ∖ {i_1} ⊇ Ω(j)`. (0-based: `g(2) = gval j L 1`, `i_1 = L[0]`.) -/
theorem theorem1c_i (P : LotSizing) (j : ℕ) (hj : 1 ≤ j) (L : List ℕ)
    (hL : P.IsRanked j L) (hΩ : P.Omega j ⊆ L.toFinset) (hlen : 1 < L.length)
    (hg : P.gval j L 1 ≤ ((P.D j : ℝ) : EReal)) :
    P.Omega j ⊆ L.toFinset.erase (L.getD 0 0) := by sorry

end FedergruenTzur.MinPred
