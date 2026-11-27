-- Prove2me | Theorems.Thm_EvenCycleListing723_Main_exploration_bound
-- name    : EvenCycleListing723.Main.exploration_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-27T05:41:37.890218+00:00
-- url     : https://prove2.me/theorems/a53bf92b-3d78-5851-b96d-8b7d16439b25
-- title:
--   Exploration cost of the max-degree BFS rounds is $O_k((n^2+t)\log n)$
-- statement:
--   Fix an integer $k\ge 2$. For a simple graph $G$ on $n$ vertices, run the round procedure of Section 3: repeatedly choose a vertex $u$ of maximum degree in the current induced graph $G_u$ (ties broken by label), stopping when the maximum degree is at most one, and delete $u$. The exploration cost is
--
--   $$W_k(G)=\sum_{u\text{ processed}}\ \sum_{\substack{v\in V(G_u)\\ \operatorname{dist}_{G_u}(u,v)\le k-1}}\deg_{G_u}(v).$$
--
--   There is a constant $C_k$, depending only on $k$, such that for every $n$ and every graph $G$ on $n$ vertices
--
--   $$W_k(G)\le C_k\,\bigl(n^2+t_{2k}(G)\bigr)\,\ell(n),\qquad \ell(n)=1+\lfloor\log_2\max(2,n)\rfloor,$$
--
--   where $t_{2k}(G)$ is the number of $2k$-cycle copies of $G$.
--
--   This is the bound established in the proof of Theorem 1.1 (p. 8): the rounds are grouped into dyadic buckets of root degree $[D,2D)$ and Lemma 3.2 is applied to the graph present at the start of each bucket.
--
--   **Formalization Note** The round sequence and exploration sum are the mission's `rounds` and `exploration` definitions.
-- source:
--   Neha Pant and Virginia Vassilevska Williams, Listing Even Cycles Even Faster, STOC 2027 submission #723, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/723.pdf, p.8, proof of Theorem 1.1 (dyadic bucketing combined with Lemma 3.2)

import Mathlib
import Definitions.Def_EvenCycleListing723_Main_Execution

set_option autoImplicit false

namespace EvenCycleListing723.Main

theorem exploration_bound (k : ℕ) (hk : 2 ≤ k) :
    ∃ C : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
      exploration G k ≤ C * (n ^ 2 + cycleCount G k) * logarithmicSize n := by sorry

end EvenCycleListing723.Main
