-- Prove2me | Theorems.Thm_EDPHardness_IntegralityGap_canonical_paths_bound
-- name    : EDPHardness.IntegralityGap.canonical_paths_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:07:46.361032+00:00
-- url     : https://prove2.me/theorems/ad8888fa-75fb-4d3b-9f1c-5951a5437a72
-- title:
--   §2.4 — |𝒫₁| ≤ n/β₁: if ℰ₁ fails, at most n/β₁ pairs are routed on their canonical paths
-- statement:
--   Let $c\ge2$, assume $\beta_1>0$, and let $H$ be a hypergraph on $n$ vertices with $\lfloor\beta_2n\rfloor$ hyperedges of size $c$ for which the event $\mathcal E_1$ does not occur (every set of $\lceil n/\beta_1\rceil$ vertices contains a hyperedge). Consider any integral routing in $G(H)$ with congestion at most $c-1$, and let $\mathcal P_1$ be the set of routed pairs whose path is their canonical path. Then
--   $$|\mathcal P_1|\le\frac n{\beta_1}.$$
--
--   Otherwise some hyperedge would have all $c$ of its vertices routed canonically, and its special edge would carry $c$ paths.
--
--   **Formalization Note** "Routed on its canonical path" means that the routing path has the vertex sequence of $P(v)$.
-- source:
--   Andrews, Chuzhoy, Guruswami, Khanna, Talwar, Zhang, Inapproximability of Edge-Disjoint Paths and Low Congestion Routing on Undirected Graphs, Combinatorica 30 (2010), p. 495, Section 2.4, Gap Analysis for EDPwC (bound on |P1|)

import Mathlib
import Definitions.Def_EDPHardness_IntegralityGap_FlowRelaxation
import Definitions.Def_EDPHardness_IntegralityGap_GapInstance

namespace EDPHardness.IntegralityGap

theorem canonical_paths_bound (n c : ℕ) (hc : 2 ≤ c) (hβ₁ : 0 < beta1 n c)
    (H : Hyp n (numEdges n c) c) (hE₁ : ¬ E1 n c H)
    (R : IntRouting (gapGraph H) (src n (numEdges n c)) (snk n (numEdges n c)) (c - 1)) :
    ((Finset.univ.filter
        (fun v : R.routed => (R.path v).support = canonicalSupport H v)).card : ℝ)
      ≤ (n : ℝ) / beta1 n c := by sorry

end EDPHardness.IntegralityGap
