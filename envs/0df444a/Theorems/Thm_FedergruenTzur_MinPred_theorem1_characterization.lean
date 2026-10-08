-- Prove2me | Theorems.Thm_FedergruenTzur_MinPred_theorem1_characterization
-- name    : FedergruenTzur.MinPred.theorem1_characterization
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T12:13:07.963548+00:00
-- url     : https://prove2.me/theorems/1034f4b8-7916-44d5-9b36-3509ab7a3007
-- title:
--   THEOREM 1(a): a ranked superset S of Ω(j) equals Ω(j) iff g(1) < g(2) < ⋯ < g(r) < ∞
-- statement:
--   This is the main theorem of Federgruen and Tzur: the characterization of the Minimal Optimal Predecessors lists.
--
--   Consider the dynamic lot size model with demands $d_i$, setup costs $K_i$, unit order costs $c_i$ and unit holding costs $h_i$, and costs $F(l,t)$, $F(t)$ given by the zero-inventory recursion (2). Fix $j \ge 1$, and let $S \subseteq \{1, \dots, j\}$ be a collection of periods which contains the $j$th Minimal Optimal Predecessors list, $\Omega(j) \subseteq S$. Number the elements of $S$ in nonascending order of their $\tilde C$-values, $S = \{i_1, \dots, i_r\}$ with $\tilde C(i_1) \ge \dots \ge \tilde C(i_r)$, periods with equal $\tilde C$-values being ranked in ascending order of their indices. Let
--   $$
--   g(1) = D(j), \qquad g(l) = G(i_l, i_{l-1}) \quad (l = 2, \dots, r),
--   $$
--   with $G$ the root (5) extended symmetrically. Then $S = \Omega(j)$ if and only if
--   $$
--   g(1) < g(2) < \dots < g(r) < \infty. \tag{6}
--   $$
--
--   The theorem turns the minimality of the candidate list into a test on consecutive pairs of a sorted list, which is what lets the forward algorithm maintain $\Omega(j)$ by local deletions and solve the general dynamic lot sizing model in $O(n \log n)$ time.
--
--   **Formalization Note.**
--   1. $\Omega(j)$ is the open-interval reading of the definition item `Omega`: $l \in \Omega(j)$ iff $l$ is the lowest-index optimal last setup period, among $\{1,\dots,j\}$, for every potential cumulative demand in some nondegenerate open interval above $D(j)$. Under the page's literal single-demand reading the "only if" direction fails when two candidate periods tie exactly at a breakpoint; the open-interval reading is the paper's own description of the list on p. 915.
--   2. $F$ is defined by the recursion (2); its optimality over all policies is the paper's Lemma 1, not formalized here. No sign assumptions are placed on the data.
--   3. $S$ is a duplicate-free list `L` (0-based), and its set of entries is `L.toFinset`; the ranking, the $g$-values and (6) are the definition item `RankedList`, with values in the extended reals so that $g(l) = \pm\infty$ is kept. The hypotheses are satisfiable for every $j \ge 1$: rank $\{1, \dots, j\}$ itself.
-- source:
--   Federgruen and Tzur, A Simple Forward Algorithm to Solve General Dynamic Lot Sizing Models with n Periods in O(n log n) or O(n) Time, Management Science 37(8), 1991, p. 915, THEOREM 1 (first paragraph) and part (a), condition (6)

import Mathlib
import Definitions.Def_FedergruenTzur_MinPred_Omega
import Definitions.Def_FedergruenTzur_MinPred_RankedList

namespace FedergruenTzur.MinPred

open LotSizing

/-- THEOREM 1(a), p. 915 (Main theorem: Characterization of the Minimal Optimal Predecessors lists).
Fix `j ≥ 1` and let `L = [i_1, …, i_r]` list a set `S` with `Ω(j) ⊆ S ⊆ {1, …, j}`, ranked in
nonascending order of `C̃`, ties in ascending period index. Then `S = Ω(j)` if and only if
`g(1) < g(2) < ⋯ < g(r) < ∞` (condition (6)). -/
theorem theorem1_characterization (P : LotSizing) (j : ℕ) (hj : 1 ≤ j) (L : List ℕ)
    (hL : P.IsRanked j L) (hΩ : P.Omega j ⊆ L.toFinset) :
    L.toFinset = P.Omega j ↔ P.Cond6 j L := by sorry

end FedergruenTzur.MinPred
