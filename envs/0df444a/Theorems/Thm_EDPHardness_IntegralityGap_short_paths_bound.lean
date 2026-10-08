-- Prove2me | Theorems.Thm_EDPHardness_IntegralityGap_short_paths_bound
-- name    : EDPHardness.IntegralityGap.short_paths_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:08:13.156981+00:00
-- url     : https://prove2.me/theorems/7b64b1a3-f5bf-4937-ae01-bc6c852765e4
-- title:
--   §2.4 — |𝒫₃| ≤ n/β₁ + 2gc(6β₂c²)^{2g+2} when ℰ₂ and ℰ₃(2g) fail
-- statement:
--   Let $c\ge2$, assume $\beta_1>0$, $\beta_2>0$, and let $g=\lceil3\beta_1\beta_2c^2\rceil$ with $10\beta_2c\le g$. Let $H$ be a hypergraph on $n$ vertices with $\lfloor\beta_2n\rfloor$ hyperedges of size $c$ for which neither $\mathcal E_2$ (more than $n/\beta_1$ vertices of degree $>10\beta_2c$) nor $\mathcal E_3(2g)$ (more than $(6\beta_2c^2)^{2g+1}$ cycles of length at most $2g$ in $G'$) occurs. In every integral routing in $G(H)$ with congestion at most $c-1$, the set $\mathcal P_3$ of pairs routed on a non-canonical path with fewer than $g$ edges satisfies
--   $$|\mathcal P_3|\le\frac n{\beta_1}+2gc\,(6\beta_2c^2)^{2g+2}.$$
--
--   The term $n/\beta_1$ accounts for the high-degree vertices; the remaining set $\mathcal P_3'$ has $|\mathcal P_3'|\le2gc(6\beta_2c^2)^{2g+2}$, because a short non-canonical path and the canonical path of a low-degree vertex together close a short cycle of $G'$.
--
--   **Formalization Note** The page bounds the discarded high-degree pairs by $n/\beta_1$ and $|\mathcal P_3'|$ separately; the statement is their sum. The hypothesis $10\beta_2c\le g$ is the page's "$g+10\beta_2c\le2g$". Lengths are counted in $G(H)$.
-- source:
--   Andrews, Chuzhoy, Guruswami, Khanna, Talwar, Zhang, Inapproximability of Edge-Disjoint Paths and Low Congestion Routing on Undirected Graphs, Combinatorica 30 (2010), pp. 495–496, Section 2.4, Gap Analysis for EDPwC (bounds on |P3| and |P′3|)

import Mathlib
import Definitions.Def_EDPHardness_IntegralityGap_FlowRelaxation
import Definitions.Def_EDPHardness_IntegralityGap_GapInstance

namespace EDPHardness.IntegralityGap

theorem short_paths_bound (n c : ℕ) (hc : 2 ≤ c) (hβ₁ : 0 < beta1 n c) (hβ₂ : 0 < beta2 n c)
    (hg : 10 * beta2 n c * c ≤ (gParam n c : ℝ))
    (H : Hyp n (numEdges n c) c) (hE₂ : ¬ E2 n c H) (hE₃ : ¬ E3 n c (2 * gParam n c) H)
    (R : IntRouting (gapGraph H) (src n (numEdges n c)) (snk n (numEdges n c)) (c - 1)) :
    ((Finset.univ.filter
        (fun v : R.routed => (R.path v).support ≠ canonicalSupport H v ∧
          (R.path v).length < gParam n c)).card : ℝ)
      ≤ (n : ℝ) / beta1 n c +
        2 * gParam n c * c * (6 * beta2 n c * (c : ℝ) ^ 2) ^ (2 * gParam n c + 2) := by sorry

end EDPHardness.IntegralityGap
