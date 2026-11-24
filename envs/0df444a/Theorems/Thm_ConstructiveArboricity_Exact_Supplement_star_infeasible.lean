-- Prove2me | Theorems.Thm_ConstructiveArboricity_Exact_Supplement_star_infeasible
-- name    : ConstructiveArboricity.Exact.Supplement.star_infeasible
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-15T10:20:14.416234+00:00
-- url     : https://prove2.me/theorems/3189bdff-e57f-4b93-ac95-1bd00a4cbfb2
-- title:
--   Lemma 4.11 — Global infeasible case for Star Insertion
-- statement:
--   Let $H$ be a finite simple graph, $r$ a specified vertex, and $k\ge1$. Suppose the edges outside the star at $r$ are partitioned into $k$ forests. Root the input forests arbitrarily and form the complete network $D$ of Definition 4.10, using their fixed input depths. Write $U$ for the star edges and $f(D)$ for the actual maximum integral flow value. Then
--
--   $$ f(D)<|U|\quad\Longrightarrow\quad H\text{ has no partition into }k\text{ forests}. $$
--
--   The nonexistence conclusion permits arbitrary recoloring of all old edges. This support validates the global rejection branch of Star Insertion, rather than merely detecting failure with the old colors fixed.
--
--   Differences from the source:
--   - encoding: finite graphs and algorithms with uniform asymptotic bounds → edge-indexed finite labels and one finite word-RAM program, with uniform positive constants; reason: labels preserve every finite graph up to relabeling; Runs charges actual instructions including memory, subroutines and output
--   - encoding: the maximum s-t flow value of D → the maximum over feasible integral values, with zero-capacity entries for absent arcs; reason: capacities are integral, so an integral maximum has the full maximum value; zero-capacity arcs cannot carry flow
-- source:
--   Gholami, Hajiaghayi, JafariRaviz, Kaviani, Mohammadkhani and Shahrezaei, Constructive Arboricity in Almost-Linear Time for Dense Graphs, STOC 2027 submission #1476 (October 2026). This is the pinned submission, not an assertion of conference acceptance. Lemma 4.11, PDF/printed p.19.

import Definitions.Def_ConstructiveArboricity_Exact_Supplement_StarNetwork

namespace ConstructiveArboricity.Exact.Supplement

/-- Lemma 4.11, p.19: failure excludes a partition after arbitrary recoloring. -/
theorem star_infeasible (G : Graph) (k : ℕ) (r : Fin G.n)
    (a : StarInput G k r) (o : Rooting G a) (hk : 1 ≤ k)
    (h : starFlowValue G a o < (starEdges G r).card) : ¬ G.Feasible k := by sorry

end ConstructiveArboricity.Exact.Supplement
