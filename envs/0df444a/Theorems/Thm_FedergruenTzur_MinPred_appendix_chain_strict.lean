-- Prove2me | Theorems.Thm_FedergruenTzur_MinPred_appendix_chain_strict
-- name    : FedergruenTzur.MinPred.appendix_chain_strict
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T12:12:14.245233+00:00
-- url     : https://prove2.me/theorems/d5b80d6f-7801-4c90-9934-85e462f56314
-- title:
--   Appendix, chains (7)–(8): under (6), i_k is strictly the cheapest entry of S for g(k) < D < g(k + 1)
-- statement:
--   In the dynamic lot size model, fix $j$ and a ranked list $S = \{i_1, \dots, i_r\} \subseteq \{1, \dots, j\}$ (nonascending $\tilde C$, ties in ascending index) with critical values $g(1) = D(j)$, $g(l) = G(i_l, i_{l-1})$, satisfying condition (6): $g(1) < g(2) < \dots < g(r) < \infty$. Fix $k \in \{1, \dots, r\}$ and a potential cumulative demand $x$ with
--
--   1. $x < g(2)$ if $k = 1$ (case (i)),
--   2. $g(k) < x < g(k+1)$ if $2 \le k \le r-1$ (case (ii)),
--   3. $x > g(r)$ if $k = r$ (case (iii))
--
--   (for $r = 1$ there is no constraint). Then $i_k$ is strictly cheaper than every other element of $S$:
--   $$
--   \pi_j(i_k, x) < \pi_j(l, x) \qquad \text{for all } l \in S \setminus \{i_k\},
--   $$
--   where $\pi_j$ is the potential cost. This is the content of the chains $F(i_k,t) < F(i_{k-1},t) < \dots < F(i_1,t)$ (7) and $F(i_k,t) < F(i_{k+1},t) < \dots < F(i_r,t)$ (8) in the proof of Theorem 1.
--
--   It establishes that, under (6), every element of the list is the unique best element of the list on its own interval of cumulative demands.
--
--   **Formalization Note.** The list is 0-based in Lean: the entry `L.getD m 0` is $i_{m+1}$, the lower bound `gval j L m < x` is absent for $m = 0$ and the upper bound `x < gval j L (m+1)` is absent for $m = r-1$. The statement does not mention $\Omega(j)$ and is stated for every real $x$; costs are potential costs, which by `potCost_spec` differ from $F(\cdot,t)$ at $x = D(t)$ by a term independent of the period.
-- source:
--   Federgruen and Tzur, A Simple Forward Algorithm to Solve General Dynamic Lot Sizing Models with n Periods in O(n log n) or O(n) Time, Management Science 37(8), 1991, p. 923, Appendix (Proof of Theorem 1), second paragraph, (i)–(iii) and chains (7)–(8)

import Mathlib
import Definitions.Def_FedergruenTzur_MinPred_Omega
import Definitions.Def_FedergruenTzur_MinPred_RankedList

namespace FedergruenTzur.MinPred

open LotSizing

/-- Appendix, p. 923, the chains (7)–(8): if a ranked list `L = [i_1, …, i_r]` satisfies (6), then
for a potential cumulative demand `x` strictly between consecutive `g`-values the entry `L[m]`
(the paper's `i_{m+1}`, 0-based) is strictly cheaper than every other entry of `L`.
The lower bound is absent for `m = 0` (the paper's case (i), `D(t) < g(2)`) and the upper bound is
absent for `m = r - 1` (case (iii), `D(t) > g(r)`). -/
theorem appendix_chain_strict (P : LotSizing) (j : ℕ) (L : List ℕ) (hL : P.IsRanked j L)
    (h6 : P.Cond6 j L) (m : ℕ) (hm : m < L.length) (x : ℝ)
    (hlow : m = 0 ∨ P.gval j L m < (x : EReal))
    (hup : L.length ≤ m + 1 ∨ (x : EReal) < P.gval j L (m + 1)) :
    ∀ l ∈ L, l ≠ L.getD m 0 → P.potCost j (L.getD m 0) x < P.potCost j l x := by sorry

end FedergruenTzur.MinPred
