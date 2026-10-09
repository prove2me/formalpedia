-- Prove2me | Theorems.Thm_CClosedGraphs_Improved_ineq_3
-- name    : CClosedGraphs.Improved.ineq_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:22:23.171769+00:00
-- url     : https://prove2.me/theorems/72466683-18a9-435b-a98b-e5a837d2976b
-- title:
--   Inequality (3), p. 9 — Σ_S |N(S) ∩ N₂(v)| ≤ |N₂(v)| 2^{c−1} ≤ min{Δ², n} 2^{c−1}
-- statement:
--   Let $c\ge1$, let $G[W]$ be $c$-closed, let $v\in W$, and let $\Delta$ bound the degree in $G[W]$ of every vertex of $W$. With $N(S)$ and $N_2(v)$ as in the setting (computed in $G[W]$) and $n=|W|$,
--   $$\sum_{\emptyset\ne S\subseteq W\cap N(v)}|N(S)\cap N_2(v)|\;\le\;|N_2(v)|\,2^{c-1}
--   \qquad\text{and}\qquad |N_2(v)|\le\min\{\Delta^2,n\}.$$
--
--   The first inequality holds because a vertex $u\in N_2(v)$ is not adjacent to $v$, so $u$ and $v$ have fewer than $c$ common neighbours and $u$ lies in $N(S)$ for few sets $S$. Together the two give inequality (3), the constraint under which the sum (2) is maximised.
--
--   **Formalization Note** $\Delta$ is any common upper bound on the degrees in $G[W]$ (the paper takes the maximum degree). The sum runs over non-empty $S$, matching the definition of $N(S)$; this only strengthens the paper's display. All quantities are natural numbers.
-- source:
--   Fox, Roughgarden, Seshadhri, Wei and Wein, Finding cliques in social networks: a new distribution-free model, arXiv:1804.07431v1, p. 9, proof of Theorem 3.1, Case 2, inequality (3)

import Mathlib
import Definitions.Def_CClosedGraphs_Improved_Setting

namespace CClosedGraphs.Improved
open Classical in
theorem ineq_3 {V : Type*} [Fintype V] [DecidableEq V] {c : ℕ} (hc : 0 < c)
    {G : SimpleGraph V} {W : Set V} (hW : IsCClosedOn c G W) {v : V} (hv : v ∈ W)
    (Δ : ℕ) (hΔ : ∀ x ∈ W, (W ∩ G.neighborSet x).ncard ≤ Δ) :
    (∑ S ∈ (Finset.univ.filter (fun x => x ∈ W ∧ G.Adj v x)).powerset.filter
          (fun S => S.Nonempty),
        (commonNbrs G S ∩ dist2In G W v).ncard) ≤ (dist2In G W v).ncard * 2 ^ (c - 1) ∧
      (dist2In G W v).ncard ≤ min (Δ ^ 2) W.ncard := by sorry
end CClosedGraphs.Improved
