-- Prove2me | Theorems.Thm_CompetitivePaging_Combining_realizable_iff
-- name    : CompetitivePaging.Combining.realizable_iff
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T13:25:46.996521+00:00
-- url     : https://prove2.me/theorems/6eff46ef-c260-43c5-8eb4-0e072dcc5aca
-- title:
--   Theorem 6 — $c^*$ is realizable iff $\sum_i 1/c(i)\le 1$
-- statement:
--   Let $m\ge1$ and let $c^*=(c(1),\dots,c(m))$ be a sequence of positive reals. Then $c^*$ is realizable — for every type $(k,n)$ of paging algorithm and every $m$ deterministic on-line algorithms $B(1),\dots,B(m)$ of that type there is one deterministic on-line algorithm $A$ of the same type that is $c(i)$-competitive against each $B(i)$ — if and only if
--   $$\sum_{1\le i\le m}\frac{1}{c(i)}\le 1 .$$
--
--   For example, with $m=2$ and $c(1)=c(2)=2$ any two paging algorithms can be combined into one that costs at most twice either of them, up to an additive constant, while no pair of ratios with $1/c(1)+1/c(2)>1$ can be achieved against every pair of algorithms.
--
--   **Formalization Note** Realizability quantifies over every type: every $k\in\mathbb N$ and every finite type $M$ with the uniform metric. The hypothesis $m\ge1$ is the paper's ("let $m$ be a positive integer"); for $m=0$ the realizability of the empty sequence would demand an algorithm of every type, which does not exist for $k=0$ servers on a nonempty vertex set.
-- source:
--   Fiat, Karp, Luby, McGeoch, Sleator, Young, Competitive Paging Algorithms, arXiv:cs/0205038v1, p. 9 (PDF p. 10), Theorem 6, eq. (1)

import Mathlib
import Definitions.Def_KServer_model
import Definitions.Def_CompetitivePaging_Combining_Realizable

namespace CompetitivePaging.Combining

/-- **Theorem 6** (Fiat, Karp, Luby, McGeoch, Sleator, Young 1991, p. 9). A sequence
`c = (c(1), …, c(m))` of positive reals is realizable if and only if `∑_{i} 1 / c(i) ≤ 1`. -/
theorem realizable_iff {m : ℕ} (hm : 0 < m) (c : Fin m → ℝ) (hc : ∀ i, 0 < c i) :
    Realizable c ↔ ∑ i, 1 / c i ≤ 1 := by sorry

end CompetitivePaging.Combining
