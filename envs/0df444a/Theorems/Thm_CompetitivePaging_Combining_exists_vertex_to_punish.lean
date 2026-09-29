-- Prove2me | Theorems.Thm_CompetitivePaging_Combining_exists_vertex_to_punish
-- name    : CompetitivePaging.Combining.exists_vertex_to_punish
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T13:23:23.292181+00:00
-- url     : https://prove2.me/theorems/af213c1b-cd20-41a0-b01c-6bf3f30fe6e3
-- title:
--   A faulting algorithm always has a server on a vertex the other algorithm does not cover
-- statement:
--   Let $S_A$ and $S_B$ be finite sets of vertices, and let $x$ be a vertex. Suppose $|S_A|=k$, $|S_B|\le k$, $x\in S_B$ and $x\notin S_A$. Then
--   $$\exists\,u\in S_A\setminus S_B .$$
--
--   In the sufficiency proof of Theorem 6, $S_A=S(A,t)$ is the set of vertices covered by $A$ just before the request $\sigma(t)=x$, and $S_B=S(B(i),t+1)$ is the set covered by $B(i)$ just after serving it. The vertex $u$ is the one from which $A$ moves a server to $\sigma(t)$ in order to punish $B(i)$; this is what gives $A$ the freedom to choose which $B(i)$ to punish at each fault.
--
--   **Formalization Note** Only the counting step of the paragraph is stated. The paragraph's final sentence ("Then $A$ can punish $B(i)$ at step $t$ by moving a server from vertex $u$ to vertex $\sigma(t)$") is not stated: under the paper's own definition of a $v$-interval, which begins with a move, it fails when $A$'s server on $u$, or $B(i)$'s server covering $u$, has not moved since the start (at most $k$ steps, absorbed by the additive constant of Theorem 6). $|S_B|\le k$ (rather than $=k$) covers algorithms that stack two servers on one vertex.
-- source:
--   Fiat, Karp, Luby, McGeoch, Sleator, Young, Competitive Paging Algorithms, arXiv:cs/0205038v1, p. 9 (PDF p. 10), §6, proof of Theorem 6 (sufficiency)

import Mathlib

namespace CompetitivePaging.Combining

/-- Fiat et al. 1991, §6, proof of Theorem 6, p. 9, the counting step: if `S(A, t)` has
cardinality `k`, `S(B(i), t + 1)` has at most `k` elements and contains the request `σ(t)`,
and `σ(t) ∉ S(A, t)`, then some vertex `u` lies in `S(A, t)` but not in `S(B(i), t + 1)`. -/
theorem exists_vertex_to_punish {M : Type} [DecidableEq M] (k : ℕ) (SA SB : Finset M) (x : M)
    (hSA : SA.card = k) (hSB : SB.card ≤ k) (hxB : x ∈ SB) (hxA : x ∉ SA) :
    ∃ u ∈ SA, u ∉ SB := by sorry

end CompetitivePaging.Combining
