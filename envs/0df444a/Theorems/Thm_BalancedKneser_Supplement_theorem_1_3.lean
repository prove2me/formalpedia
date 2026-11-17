-- Prove2me | Theorems.Thm_BalancedKneser_Supplement_theorem_1_3
-- name    : BalancedKneser.Supplement.theorem_1_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T13:14:05.735856+00:00
-- url     : https://prove2.me/theorems/eae1f4a7-318c-48a1-b8e3-b33338518a1f
-- title:
--   Theorem 1.3 — $\operatorname{ind}_{\mathbb Z_2}B(G_{n,r})\le 4r-5$ for $n\ge 2r-1$, with equality for $r=2,3$
-- statement:
--   Let $G_{n,r}=KG(2n,n,r)$ be the balanced generalized Kneser graph: its vertices are the $n$-subsets of $[2n]$, and two distinct sets are adjacent when they share fewer than $r$ elements. Let $B(G_{n,r})$ be its box complex (pairs of probability distributions on the vertices whose positive supports span a complete bipartite subgraph), with the involution exchanging the two sides, and let $\operatorname{ind}_{\mathbb Z_2}$ be the least $d$ admitting a continuous map $B(G_{n,r})\to S^d$ that sends the exchange to $x\mapsto -x$.
--
--   For all integers $r\ge2$ and $n\ge 2r-1$,
--   $$
--   \operatorname{ind}_{\mathbb Z_2}B(G_{n,r})\ \le\ 4r-5,
--   $$
--   and equality holds for $r=2$ and $r=3$: $\operatorname{ind}_{\mathbb Z_2}B(G_{n,2})=3$ for $n\ge3$ and $\operatorname{ind}_{\mathbb Z_2}B(G_{n,3})=7$ for $n\ge5$.
--
--   Through the standard bound $\chi(G)\ge\operatorname{ind}_{\mathbb Z_2}B(G)+2$, the index certifies at most $4r-3$ colors for $G_{n,r}$ in this range, i.e. only five colors for $r=2$ and nine for $r=3$; the chromatic lower bounds $\chi(G_{n,2})\ge6$ and $\chi(G_{n,3})\ge10$ of Theorem 1.2 therefore go beyond what the index can give.
--
--   **Formalization Note** The upper bound is stated in $\mathbb N\cup\{\infty\}$, where the index of a space with no equivariant sphere map is $\infty$; so it asserts that an equivariant map to some $S^d$ with $d\le4r-5$ exists. The equality clause adds that no equivariant map $B(G_{n,r})\to S^d$ exists for $d<4r-5$. The expressions $4r-5$ and $2r-1$ are natural-number subtractions, exact since $r\ge2$.
--
--   Differences from the source: none.
-- source:
--   Alipour, Jafari, Balanced Fair Division and Generalized Kneser Graphs, arXiv:2611.04486v1, Theorem 1.3, p.2 (PDF p.4); proof §10.1–10.3, pp.24–26 (PDF pp.26–28)

import Mathlib
import Definitions.Def_BalancedKneser_KG
import Definitions.Def_BalancedKneser_Supplement_boxComplex

namespace BalancedKneser.Supplement

/-- **Theorem 1.3** (Alipour–Jafari, *Balanced Fair Division and Generalized Kneser Graphs*,
arXiv:2611.04486v1, §1, p.2 (PDF p.4); proof §10, pp.24–26 (PDF pp.26–28)): for `r ≥ 2` and
`n ≥ 2r − 1`, `ind_{ℤ₂} B(G_{n,r}) ≤ 4r − 5`, and equality holds for `r = 2` and `r = 3`.

Formalization Note: `G_{n,r}` is the published `BalancedKneser.Gnr n r = KG(2n, n, r)`;
`B(G)` is the weighted-pair model of §9.1 (`boxComplex`) and `ind_{ℤ₂}` is `z2Index : ℕ∞`
(the infimum of the empty set is `∞`, so the bound is not vacuous). `4r − 5` and `2r − 1` are
natural-number subtractions, exact for `r ≥ 2`. -/
theorem theorem_1_3 (n r : ℕ) (hr : 2 ≤ r) (hn : 2 * r - 1 ≤ n) :
    z2Index (BalancedKneser.Gnr n r) ≤ ((4 * r - 5 : ℕ) : ℕ∞) ∧
      (r = 2 ∨ r = 3 → z2Index (BalancedKneser.Gnr n r) = ((4 * r - 5 : ℕ) : ℕ∞)) := by sorry

end BalancedKneser.Supplement
