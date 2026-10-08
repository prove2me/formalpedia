-- Prove2me | Theorems.Thm_FedergruenTzur_MinPred_theorem1c_ii
-- name    : FedergruenTzur.MinPred.theorem1c_ii
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T12:12:55.461583+00:00
-- url     : https://prove2.me/theorems/696906c7-eeb4-4dfc-9b79-67b8cc8003c5
-- title:
--   THEOREM 1(c)(ii): for k = 2, …, r − 1, if g(k + 1) ≤ g(k) then (S∖{i_k}) ⊇ Ω(j)
-- statement:
--   In the dynamic lot size model with costs given by the recursion (2), fix $j \ge 1$ and let $S = \{i_1, \dots, i_r\}$ with $\Omega(j) \subseteq S \subseteq \{1, \dots, j\}$ be ranked in nonascending order of $\tilde C$-values, ties in ascending order of period index, with critical values $g(1) = D(j)$ and $g(l) = G(i_l, i_{l-1})$. For $k = 2, \dots, r-1$: if $g(k+1) \le g(k)$, then
--   $$
--   S \setminus \{i_k\} \supseteq \Omega(j).
--   $$
--
--   An interior element whose interval $(g(k), g(k+1))$ is empty is never the unique best last setup period and may be deleted from the list.
--
--   **Formalization Note.** 0-based in Lean: the paper's $k$ is $m + 1$, so $k \in \{2, \dots, r-1\}$ is $1 \le m$ and $m + 1 < r$; $i_k$ is `L.getD m 0`, $g(k)$ is `gval j L m` and $g(k+1)$ is `gval j L (m+1)`. The comparison is in the extended reals. $\Omega(j)$ is taken in the open-interval reading.
-- source:
--   Federgruen and Tzur, A Simple Forward Algorithm to Solve General Dynamic Lot Sizing Models with n Periods in O(n log n) or O(n) Time, Management Science 37(8), 1991, p. 915, THEOREM 1(c)(ii)

import Mathlib
import Definitions.Def_FedergruenTzur_MinPred_Omega
import Definitions.Def_FedergruenTzur_MinPred_RankedList

namespace FedergruenTzur.MinPred

open LotSizing

/-- THEOREM 1(c)(ii), p. 915: for `k = 2, …, r - 1`, if `g(k + 1) ≤ g(k)` then
`S ∖ {i_k} ⊇ Ω(j)`. (0-based: `k = m + 1`, `i_k = L[m]`, `g(k) = gval j L m`,
`g(k + 1) = gval j L (m + 1)`, and `k ∈ {2, …, r - 1}` is `1 ≤ m`, `m + 1 < r`.) -/
theorem theorem1c_ii (P : LotSizing) (j : ℕ) (hj : 1 ≤ j) (L : List ℕ)
    (hL : P.IsRanked j L) (hΩ : P.Omega j ⊆ L.toFinset) (m : ℕ) (hm : 1 ≤ m)
    (hmr : m + 1 < L.length) (hg : P.gval j L (m + 1) ≤ P.gval j L m) :
    P.Omega j ⊆ L.toFinset.erase (L.getD m 0) := by sorry

end FedergruenTzur.MinPred
