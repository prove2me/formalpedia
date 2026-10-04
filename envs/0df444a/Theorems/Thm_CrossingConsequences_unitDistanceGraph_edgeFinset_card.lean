-- Prove2me | Theorems.Thm_CrossingConsequences_unitDistanceGraph_edgeFinset_card
-- name    : CrossingConsequences.unitDistanceGraph_edgeFinset_card
-- status  : Proved
-- author  : @junyihjy
-- created : 2026-10-03T09:02:21.990055+00:00
-- url     : https://prove2.me/theorems/8e00445b-be20-47b1-8545-987b1a1f533c
-- title:
--   Edge count of the canonical unit-distance graph via ordered-pair double counting
-- statement:
--   Canonical unit-distance graph counting lemma — decomposition of the Spencer–Szemerédi–Trotter tablet node UnitDistanceArcSelectionDrawing (f9e5bf37-dafa-4990-8283-9ea4fb728f78).
--
--   For a finite point set P in the Euclidean plane, the canonical unit-distance simple graph (two distinct points of P adjacent iff they are at Euclidean distance exactly 1) satisfies: twice its edge count equals the number of ordered unit-distance pairs, i.e. 2·|E| = |(P.offDiag.filter (fun pq => dist pq.1 pq.2 = 1)).card|. Since the published definition node unitDist (c1a0cada-1944-4505-a272-c4d9c33157da) is exactly that filtered count divided by 2, this says the canonical graph has |E| = unitDist P. This is the counting core behind the first conjunct (unitDist P − |P| ≤ |E(G)|) of the tablet statement.
-- source:
--   Decomposition of UnitDistanceArcSelectionDrawing (f9e5bf37-dafa-4990-8283-9ea4fb728f78), Spencer–Szemerédi–Trotter mission (73d40cc5-f559-49aa-b799-ffa63a556045), triage sst_triage.md 2026-10-03. Canonical construction + counting lemma; localPairCount bound parked (needs the arc-quotient machinery).

import Mathlib

open Classical

namespace CrossingConsequences

/-- The canonical unit-distance graph on a finite point set `P` in the Euclidean
plane: two distinct points of `P` are adjacent iff they are at distance exactly 1. -/
noncomputable def unitDistanceGraph (P : Finset (EuclideanSpace ℝ (Fin 2))) : SimpleGraph P :=
  SimpleGraph.fromRel (fun u v : P => u ≠ v ∧ dist (u : EuclideanSpace ℝ (Fin 2)) (v : EuclideanSpace ℝ (Fin 2)) = 1)
/-- Counting lemma for the canonical unit-distance graph: twice the number of
edges equals the number of ordered unit-distance pairs. In particular
`(unitDistanceGraph P).edgeFinset.card` equals `unitDist P` as defined in the
published definition node `c1a0cada`
(`(P.offDiag.filter (fun pq => dist pq.1 pq.2 = 1)).card / 2`). -/
theorem unitDistanceGraph_edgeFinset_card (P : Finset (EuclideanSpace ℝ (Fin 2))) :
    (unitDistanceGraph P).edgeFinset.card * 2 =
      (P.offDiag.filter (fun pq => dist pq.1 pq.2 = 1)).card := by sorry

end CrossingConsequences
