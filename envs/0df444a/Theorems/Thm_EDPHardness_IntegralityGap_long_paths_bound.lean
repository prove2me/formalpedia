-- Prove2me | Theorems.Thm_EDPHardness_IntegralityGap_long_paths_bound
-- name    : EDPHardness.IntegralityGap.long_paths_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:07:53.75341+00:00
-- url     : https://prove2.me/theorems/59007019-3352-4e60-97ef-ab1772153670
-- title:
--   §2.4 — |𝒫₂| ≤ n/β₁: at most n/β₁ pairs use non-canonical paths of length ≥ g
-- statement:
--   Let $c\ge2$, assume $\beta_1>0$ and $\beta_2\ge1$, let $g=\lceil3\beta_1\beta_2c^2\rceil$, and let $H$ be any hypergraph on $n$ vertices with $\lfloor\beta_2n\rfloor$ hyperedges of size $c$. In every integral routing in $G(H)$ with congestion at most $c-1$, the set $\mathcal P_2$ of pairs routed on a non-canonical path with at least $g$ edges satisfies
--   $$|\mathcal P_2|\le\frac n{\beta_1}.$$
--
--   The reason is capacity: $G(H)$ has at most $3\beta_2cn$ edges, so the total length of all routing paths is at most $3\beta_2c^2n$, and $3\beta_2c^2n/g\le n/\beta_1$.
--
--   **Formalization Note** Length is the number of edges of $G(H)$ on the path. The paper's count "at most $3\beta_2cn$ edges" uses $\lfloor\beta_2n\rfloor\le\beta_2n$ hyperedges and $\beta_2c$ large; the hypothesis $\beta_2\ge1$ makes it hold (it holds in the regime of Theorem 5).
-- source:
--   Andrews, Chuzhoy, Guruswami, Khanna, Talwar, Zhang, Inapproximability of Edge-Disjoint Paths and Low Congestion Routing on Undirected Graphs, Combinatorica 30 (2010), p. 495, Section 2.4, Gap Analysis for EDPwC (bound on |P2|)

import Mathlib
import Definitions.Def_EDPHardness_IntegralityGap_FlowRelaxation
import Definitions.Def_EDPHardness_IntegralityGap_GapInstance

namespace EDPHardness.IntegralityGap

theorem long_paths_bound (n c : ℕ) (hc : 2 ≤ c) (hβ₁ : 0 < beta1 n c) (hβ₂ : 1 ≤ beta2 n c)
    (H : Hyp n (numEdges n c) c)
    (R : IntRouting (gapGraph H) (src n (numEdges n c)) (snk n (numEdges n c)) (c - 1)) :
    ((Finset.univ.filter
        (fun v : R.routed => (R.path v).support ≠ canonicalSupport H v ∧
          gParam n c ≤ (R.path v).length)).card : ℝ)
      ≤ (n : ℝ) / beta1 n c := by sorry

end EDPHardness.IntegralityGap
