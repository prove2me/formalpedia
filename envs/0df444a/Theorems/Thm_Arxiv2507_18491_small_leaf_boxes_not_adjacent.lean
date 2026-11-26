-- Prove2me | Theorems.Thm_Arxiv2507_18491_small_leaf_boxes_not_adjacent
-- name    : Arxiv2507_18491.small_leaf_boxes_not_adjacent
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-26T13:02:51.456502+00:00
-- url     : https://prove2.me/theorems/2b8ef63c-6657-4f3b-b868-d12d7ec3e2f7
-- title:
--   Section 3.4.1: leaf boxes smaller than $d_{gap}/2$ are never adjacent
-- statement:
--   Let $T$ be the set of effective locations of the targets and $S$ the set of equivalent polarization coordinates of the sources of a reaction field component. Let $d_{gap}$ be a lower bound for their distances along $z$: $|z_p-z_q|\ge d_{gap}$ for all $p\in T$, $q\in S$ (for example their minimum). If a target box and a source box both have side lengths smaller than $d_{gap}/2$, and each contains at least one of its points, then the two closed boxes are disjoint. In particular they are not adjacent, so no direct (near-field) interaction between them is needed.
--
--   **Formalization Note** Boxes are closed axis-parallel cubes given by centre and side length. The paper's further estimate that $O(N^{2/3})$ adjacent box pairs occur for particles in the same or neighbouring layers is a heuristic count and is not formalized.
-- source:
--   Yuan, Wang, Zhang and Cai, Fast multipole method for Maxwell's equations in layered media, arXiv:2507.18491v1 (2025), claim c037; Section 3.4.1, first paragraph, PDF p. 17

import Mathlib
import Definitions.Def_Arxiv2507_18491_Basic

open MeasureTheory Filter Topology

namespace Arxiv2507_18491

theorem small_leaf_boxes_not_adjacent (T S : Set (ℝ × ℝ × ℝ)) (dgap : ℝ)
    (hgap : ∀ p ∈ T, ∀ q ∈ S, dgap ≤ |p.2.2 - q.2.2|) (ct cs : ℝ × ℝ × ℝ) (ht hs : ℝ)
    (ht0 : 0 < ht) (hs0 : 0 < hs) (hht : ht < dgap / 2) (hhs : hs < dgap / 2)
    (hT : ∃ p ∈ T, p ∈ box ct ht) (hS : ∃ q ∈ S, q ∈ box cs hs) :
    Disjoint (box ct ht) (box cs hs) := by sorry

end Arxiv2507_18491
