-- Prove2me | Theorems.Thm_FedergruenTzur_MinPred_theorem1b_first_optimal
-- name    : FedergruenTzur.MinPred.theorem1b_first_optimal
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T12:12:31.729258+00:00
-- url     : https://prove2.me/theorems/c09212c2-9601-49ca-8fff-d43f19dd1f51
-- title:
--   THEOREM 1(b): if (6) holds then i_1 = l(j), an optimal last setup period for the horizon j
-- statement:
--   In the dynamic lot size model with costs given by the recursion (2), fix $j \ge 1$ and let $S = \{i_1, \dots, i_r\}$ with $\Omega(j) \subseteq S \subseteq \{1, \dots, j\}$ be ranked in nonascending order of $\tilde C$-values, ties in ascending order of period index, with critical values $g(1) = D(j)$ and $g(l) = G(i_l, i_{l-1})$. If condition (6), $g(1) < g(2) < \dots < g(r) < \infty$, holds, then the first element $i_1$ is an optimal last setup period for the horizon $j$:
--   $$
--   F(i_1, j) = F(j).
--   $$
--
--   This is the paper's "$i_1 = l(j)$", where $l(j)$ denotes an optimal period for the last setup when minimizing the cost of the first $j$ periods (§2, p. 914). It means the forward algorithm reads off $l(j)$ and $F(j)$ from the head of its list in constant time.
--
--   **Formalization Note.** The conclusion is stated as: the list has a first entry $i_1$ and $F(i_1, j) = F(j)$, so it is not vacuous on an empty list. $\Omega(j)$ is taken in the open-interval reading; $F$ is defined by (2).
-- source:
--   Federgruen and Tzur, A Simple Forward Algorithm to Solve General Dynamic Lot Sizing Models with n Periods in O(n log n) or O(n) Time, Management Science 37(8), 1991, p. 915, THEOREM 1(b); l(j) as defined on p. 914, §2, first paragraph

import Mathlib
import Definitions.Def_FedergruenTzur_MinPred_Omega
import Definitions.Def_FedergruenTzur_MinPred_RankedList

namespace FedergruenTzur.MinPred

open LotSizing

/-- THEOREM 1(b), p. 915: if a ranked list `L = [i_1, …, i_r]` of periods in `{1, …, j}` contains
`Ω(j)` and satisfies (6), then its first entry `i_1` is an optimal last setup period for the horizon
`j`, i.e. `F(i_1, j) = F(j)` (the paper's `i_1 = l(j)`). -/
theorem theorem1b_first_optimal (P : LotSizing) (j : ℕ) (hj : 1 ≤ j) (L : List ℕ)
    (hL : P.IsRanked j L) (hΩ : P.Omega j ⊆ L.toFinset) (h6 : P.Cond6 j L) :
    ∃ i₁, L.head? = some i₁ ∧ P.Flast i₁ j = P.Fopt j := by sorry

end FedergruenTzur.MinPred
