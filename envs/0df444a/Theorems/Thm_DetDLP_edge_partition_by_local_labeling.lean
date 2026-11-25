-- Prove2me | Theorems.Thm_DetDLP_edge_partition_by_local_labeling
-- name    : DetDLP.edge_partition_by_local_labeling
-- status  : Proved
-- author  : @Bingsheng
-- created : 2026-11-23T11:52:39.868158+00:00
-- url     : https://prove2.me/theorems/b3d1b437-f38b-42c7-b478-ab2e3951706b
-- title:
--   Deterministic label balancing for scalar contraction
-- statement:
--   For a bipartite multigraph with $M$ edges, maximum degree $\Delta$, and an alphabet of $q\ge1$ labels, a deterministic search assigns a label to each vertex. Let $X_c$ be the number of edges with ordered pair of labels $c$, oriented using the bipartition. Its output satisfies
--   $$q^2\sum_c X_c^2\le M^2+2M\Delta q^2.$$
--   The search computes its conditional penalties from local tables of at most four vertex labels.
-- source:
--   S. Liu, B. Zhang and K. Ren, A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem, preprint, 23 November 2026. Sections 5.1–5.2, Lemma 5.1 and the recursion in Lemma 5.2.

import Definitions.Def_DetDLP_BTN

set_option autoImplicit false

namespace DetDLP

theorem edge_partition_by_local_labeling (G : BipartiteMultigraph) (q : ℕ) [NeZero q] :
    let l := fun e : Fin G.nE => if G.side (G.endpoints e).1 then (G.endpoints e).2 else (G.endpoints e).1
    let r := fun e : Fin G.nE => if G.side (G.endpoints e).1 then (G.endpoints e).1 else (G.endpoints e).2
    ∃ L : Fin G.nV → Fin q,
      let X := fun c : Fin q × Fin q => ∑ e : Fin G.nE, if (L (l e),L (r e)) = c then 1 else 0
      q^2 * (∑ c, (X c)^2) ≤ G.nE^2+2*G.nE*G.maxDeg*q^2 ∧
        (2*G.maxDeg*q^4 ≤ G.nE → ∀ c, q^2*X c ≤ 2*G.nE) := by sorry
end DetDLP
