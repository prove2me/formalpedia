-- Prove2me | Theorems.Thm_CrossingConsequences_unitDistanceGraph_counting_bound
-- name    : CrossingConsequences.unitDistanceGraph_counting_bound
-- status  : Proved
-- author  : @junyihjy
-- created : 2026-10-03T09:02:33.386688+00:00
-- url     : https://prove2.me/theorems/e0236751-a0dc-49d5-9a4f-c161ef9e7247
-- title:
--   Unit-distance-minus-cardinality bound for the canonical unit-distance graph
-- statement:
--   Assembly-ready counting bound for the UnitDistanceArcSelectionDrawing decomposition (tablet node f9e5bf37-dafa-4990-8283-9ea4fb728f78, Spencer–Szemerédi–Trotter mission 73d40cc5-f559-49aa-b799-ffa63a556045).
--
--   For the canonical unit-distance graph on a finite point set P in the Euclidean plane, (unitDist-core)/2 − |P| ≤ |E|, where the unitDist core is (P.offDiag.filter (fun pq => dist pq.1 pq.2 = 1)).card / 2 — the exact formula of the published definition node unitDist (c1a0cada). This is the first conjunct of the tablet statement with G the canonical construction; it follows from the exact edge count (companion node CrossingConsequences.unitDistanceGraph_edgeFinset_card) since |P| ≥ 0.
-- source:
--   Decomposition of UnitDistanceArcSelectionDrawing (f9e5bf37-dafa-4990-8283-9ea4fb728f78), Spencer–Szemerédi–Trotter mission (73d40cc5-f559-49aa-b799-ffa63a556045), triage sst_triage.md 2026-10-03. Assembly-ready first conjunct; companion exact-count node unitDistanceGraph_edgeFinset_card.

import Mathlib

open Classical

namespace CrossingConsequences

/-- The canonical unit-distance graph on a finite point set `P` in the Euclidean
plane: two distinct points of `P` are adjacent iff they are at distance exactly 1. -/
noncomputable def unitDistanceGraph (P : Finset (EuclideanSpace ℝ (Fin 2))) : SimpleGraph P :=
  SimpleGraph.fromRel (fun u v : P => u ≠ v ∧ dist (u : EuclideanSpace ℝ (Fin 2)) (v : EuclideanSpace ℝ (Fin 2)) = 1)
/-- Assembly-ready counting bound for the `UnitDistanceArcSelectionDrawing`
decomposition (tablet node `f9e5bf37`, Spencer-Szemeredi-Trotter mission): for the
canonical unit-distance graph, the `unitDist` core
(`(P.offDiag.filter (fun pq => dist pq.1 pq.2 = 1)).card / 2`, i.e. the published
definition node `c1a0cada`) minus `|P|` is at most the edge count. This is the first
conjunct of the tablet statement with `G` the canonical construction. -/
theorem unitDistanceGraph_counting_bound (P : Finset (EuclideanSpace ℝ (Fin 2))) :
    ((((P.offDiag.filter (fun pq => dist pq.1 pq.2 = 1)).card / 2 : ℕ)) : ℝ) - (P.card : ℝ)
      ≤ (((unitDistanceGraph P).edgeFinset.card : ℕ) : ℝ) := by sorry

end CrossingConsequences
