-- Prove2me | Theorems.Thm_CClosedGraphs_Peeling_peel_step
-- name    : CClosedGraphs.Peeling.peel_step
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T20:20:30.258115+00:00
-- url     : https://prove2.me/theorems/99e438ef-c9fe-4051-94ec-3118d56b2c2b
-- title:
--   §2.1, pp. 7–8 — peeling a vertex in no bad pair: F(n, c) ≤ F(n − 1, c) + 3^{(c−1)/3} n
-- statement:
--   Let $c$ be a positive integer, $G$ a finite simple graph, $W$ a set of vertices and $v\in W$ a vertex that is in no bad pair of $G[W]$, i.e. every $u\in W$, $u\ne v$, not adjacent to $v$ has fewer than $c$ common neighbours with $v$ inside $W$. Then
--   $$\mathrm{mc}(G[W])\ \le\ \mathrm{mc}(G[W\setminus\{v\}]) + 3^{(c-1)/3}\,|W|.$$
--
--   This is the recursive inequality $F(n,c)\le F(n-1,c)+3^{(c-1)/3}n$ of the proof of Theorem 2.1, in the form of the remark after it: "the proof is valid as long as $|N(u)\cap N(v)|<c$ for all vertices $u\notin N(v)$", so each recursive level only needs a vertex in no bad pair. Iterating it along the ordering of a weakly $c$-closed graph proves Theorem 2.2.
--
--   **Formalization Note** The paper's $n$ is $|W|$, the number of vertices of the current graph $G[W]$; $3^{(c-1)/3}$ is a real power.
-- source:
--   Fox, Roughgarden, Seshadhri, Wei and Wein, Finding cliques in social networks: a new distribution-free model, arXiv:1804.07431v1, pp. 7–8, §2.1, proof of Theorem 2.1 (recursive inequality) and the remark after it

import Mathlib
import Definitions.Def_CClosedGraphs_Peeling_Setting

namespace CClosedGraphs.Peeling
theorem peel_step {V : Type*} [Fintype V] [DecidableEq V] (c : ℕ) (hc : 0 < c)
    (G : SimpleGraph V) (W : Set V) (v : V) (hv : v ∈ W)
    (hbad : ∀ w : V, ¬ IsBadPairIn c G W v w) :
    (numMaxCliquesIn G W : ℝ) ≤
      (numMaxCliquesIn G (W \ {v}) : ℝ) + (3 : ℝ) ^ (((c : ℝ) - 1) / 3) * (W.ncard : ℝ) := by sorry
end CClosedGraphs.Peeling
