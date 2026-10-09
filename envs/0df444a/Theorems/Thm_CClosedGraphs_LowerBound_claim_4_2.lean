-- Prove2me | Theorems.Thm_CClosedGraphs_LowerBound_claim_4_2
-- name    : CClosedGraphs.LowerBound.claim_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:22:16.557506+00:00
-- url     : https://prove2.me/theorems/a8036752-3142-4c7d-8a63-9f662a06e74e
-- title:
--   Claim 4.2, p. 12 — the blow-up of a girth-5 graph by cliques of size c/2 is c-closed
-- statement:
--   Let $H$ be a finite graph of girth at least $5$, let $h \ge 1$ be an integer, and let $H^{(h)}$ be the blow-up of $H$ in which each vertex $x$ becomes a clique $U_x$ of $h$ vertices, the bipartite graph between $U_x$ and $U_y$ is $K_{h,h}$ minus a perfect matching when $xy \in E(H)$, and there are no edges between $U_x$ and $U_y$ otherwise. Then, with $c = 2h$,
--   $$
--   H^{(h)} \ \text{is } c\text{-closed}.
--   $$
--
--   This is the first half of the lower-bound construction: the graph built from $H$ satisfies the triadic-closure condition with parameter $c$.
--
--   **Formalization Note** The paper's $c$ is even and $|U_x| = c/2$; here $h = c/2$ and the conclusion is stated for $c = 2h$. The paper builds $H^{(h)}$ from one extremal girth-$5$ graph, but its proof uses only that $H$ has girth at least $5$, so the claim is stated for every such $H$ (girth via Mathlib's `egirth`, $\infty$ for forests). The perfect matching is fixed as $(x,i) \leftrightarrow (y,i)$, one admissible choice in the paper's construction. For $h = 1$ the blow-up is edgeless and the claim is still true.
-- source:
--   Fox, Roughgarden, Seshadhri, Wei and Wein, Finding cliques in social networks: a new distribution-free model, arXiv:1804.07431v1, p. 12, Claim 4.2

import Mathlib
import Definitions.Def_CClosedGraphs_LowerBound_Setting

namespace CClosedGraphs.LowerBound
theorem claim_4_2 {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) (h : ℕ)
    (hh : 1 ≤ h) (hH : 5 ≤ H.egirth) : CClosedGraphs.Peeling.IsCClosed (2 * h) (blowUp H h) := by sorry
end CClosedGraphs.LowerBound
