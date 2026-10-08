-- Prove2me | Theorems.Thm_FedergruenTzur_MinPred_theorem1c_iii
-- name    : FedergruenTzur.MinPred.theorem1c_iii
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T12:12:44.177224+00:00
-- url     : https://prove2.me/theorems/9aa06ebd-5b76-413d-a4bb-8ed2d2bcec27
-- title:
--   THEOREM 1(c)(iii): if g(r) = ∞ then (S∖{i_r}) ⊇ Ω(j)
-- statement:
--   In the dynamic lot size model with costs given by the recursion (2), fix $j \ge 1$ and let $S = \{i_1, \dots, i_r\}$ with $\Omega(j) \subseteq S \subseteq \{1, \dots, j\}$ be ranked in nonascending order of $\tilde C$-values, ties in ascending order of period index, with critical values $g(1) = D(j)$ and $g(l) = G(i_l, i_{l-1})$. If $g(r) = \infty$, then
--   $$
--   S \setminus \{i_r\} \supseteq \Omega(j).
--   $$
--
--   A last element that never overtakes its predecessor may be deleted from the list.
--
--   **Formalization Note.** 0-based in Lean: $g(r)$ is `gval j L (r-1)` and $i_r$ is `L.getD (r-1) 0`. For $r = 1$ the hypothesis cannot hold, since $g(1) = D(j)$ is finite. $\Omega(j)$ is taken in the open-interval reading.
-- source:
--   Federgruen and Tzur, A Simple Forward Algorithm to Solve General Dynamic Lot Sizing Models with n Periods in O(n log n) or O(n) Time, Management Science 37(8), 1991, p. 915, THEOREM 1(c)(iii)

import Mathlib
import Definitions.Def_FedergruenTzur_MinPred_Omega
import Definitions.Def_FedergruenTzur_MinPred_RankedList

namespace FedergruenTzur.MinPred

open LotSizing

/-- THEOREM 1(c)(iii), p. 915: if `g(r) = ∞` then `S ∖ {i_r} ⊇ Ω(j)`.
(0-based: `g(r) = gval j L (r - 1)`, `i_r = L[r - 1]`.) -/
theorem theorem1c_iii (P : LotSizing) (j : ℕ) (hj : 1 ≤ j) (L : List ℕ)
    (hL : P.IsRanked j L) (hΩ : P.Omega j ⊆ L.toFinset) (hlen : 0 < L.length)
    (hg : P.gval j L (L.length - 1) = ⊤) :
    P.Omega j ⊆ L.toFinset.erase (L.getD (L.length - 1) 0) := by sorry

end FedergruenTzur.MinPred
