-- Prove2me | Theorems.Thm_EdmondsKarp_ShortestPath_pathArcs_chain
-- name    : EdmondsKarp.ShortestPath.pathArcs_chain
-- status  : Proved
-- author  : @arexychen
-- created : 2026-10-02T19:31:03.290497+00:00
-- url     : https://prove2.me/theorems/83291916-6509-4928-b9ad-c292f5176a64
-- title:
--   Consecutive path arcs are a relational chain
-- statement:
--   For any binary relation on vertices, every consecutive pair in a list satisfies the relation if and only if that list is a chain for the relation.
-- source:
--   Auxiliary directed-path lemmas for Edmonds and Karp (1972), §1.1 p. 249 and §1.2 pp. 251–252. DOI: 10.1145/321694.321699.

import Definitions.Def_EdmondsKarp_ShortestPath_Augmentation
open EdmondsKarp.ShortestPath

theorem EdmondsKarp.ShortestPath.pathArcs_chain {V : Type} [Fintype V] [DecidableEq V] (R : V → V → Prop) (P : List V) :
    (∀ e ∈ pathArcs P, R e.1 e.2) ↔ P.IsChain R := by sorry
