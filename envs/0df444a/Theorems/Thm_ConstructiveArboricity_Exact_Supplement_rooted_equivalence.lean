-- Prove2me | Theorems.Thm_ConstructiveArboricity_Exact_Supplement_rooted_equivalence
-- name    : ConstructiveArboricity.Exact.Supplement.rooted_equivalence
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T10:21:19.11175+00:00
-- url     : https://prove2.me/theorems/d65a2ccc-8452-475e-ad02-b6c9a06981d9
-- title:
--   Lemma 5.3 — Forests and rooted in-arborescence partitions
-- statement:
--   Let $G$ be a finite simple graph and supply any $k$-out orientation. Construct $O_r$ by adding a fresh root $r$, retaining every original oriented edge, and adding $k-d^+(v)$ separate arcs from each old vertex $v$ to $r$. Then
--
--   $$ G\text{ has a }k\text{-forest partition}\quad\Longleftrightarrow\quad A(O_r)\text{ has a partition into }k\text{ in-arborescences toward }r. $$
--
--   Every arc, including each parallel copy, belongs to exactly one class on the right. Each class is a spanning multigraph tree with one outgoing arc at each old vertex. The equivalence holds for the particular supplied orientation, including $k=0$ and empty inputs. This support justifies the rooted reduction independently of the tree-packing algorithm.
--
--   Differences from the source:
--   - encoding: finite graphs and algorithms with uniform asymptotic bounds → edge-indexed finite labels and one finite word-RAM program, with uniform positive constants; reason: labels preserve every finite graph up to relabeling; Runs charges actual instructions including memory, subroutines and output
--   - encoding: a new root and parallel added arcs; in-arborescences directed toward it → an Option vertex carrier, separate deficit-copy identities, and spanning multigraph trees with one outgoing arc at every old vertex; reason: the fresh root has no outgoing arcs, so these spanning trees are exactly the toward-root in-arborescences; all parallel copies remain distinct
-- source:
--   Gholami, Hajiaghayi, JafariRaviz, Kaviani, Mohammadkhani and Shahrezaei, Constructive Arboricity in Almost-Linear Time for Dense Graphs, STOC 2027 submission #1476 (October 2026). This is the pinned submission, not an assertion of conference acceptance. Lemma 5.3, PDF/printed p.28.

import Definitions.Def_ConstructiveArboricity_Exact_Supplement_Rooted

namespace ConstructiveArboricity.Exact.Supplement

/-- Lemma 5.3, p.28, for the arbitrary supplied orientation and all arc identities. -/
theorem rooted_equivalence (G : Graph) (k : ℕ) (tail : Fin G.m → Fin G.n)
    (h : G.IsKOut k tail) : G.Feasible k ↔ RootedPartition G k tail := by sorry

end ConstructiveArboricity.Exact.Supplement
