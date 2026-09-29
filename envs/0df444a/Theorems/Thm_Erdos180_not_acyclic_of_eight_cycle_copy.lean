-- Prove2me | Theorems.Thm_Erdos180_not_acyclic_of_eight_cycle_copy
-- name    : Erdos180.not_acyclic_of_eight_cycle_copy
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-04T02:04:24.332679+00:00
-- url     : https://prove2.me/theorems/5ebc6bdc-2d50-4a85-9500-69a27bfc6362
-- title:
--   A graph containing an eight-cycle is not acyclic
-- statement:
--   If a graph contains a copy of $C_8$ then it is not acyclic.
--
--   Theorem 1.1 of the source requires every member of $\mathcal{F}$ to contain a cycle. Each
--   member of $\mathcal{J}$ contains $S_2$ and each member of $\mathcal{K}$ contains $S_3$, and a
--   subdivided $K_{3,k}$ contains an eight-cycle — the subdivision of a four-cycle of
--   $K_{3,k}$.
-- source:
--   https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/CompactnessAndDegeneracy.lean#L1726-L1734

import Definitions.Def_erdos180_core4
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Circulant

open Erdos180
open Finset SimpleGraph

theorem Erdos180.not_acyclic_of_eight_cycle_copy
    {α : Type*} {graph : SimpleGraph α}
    (copy : SimpleGraph.Copy (SimpleGraph.cycleGraph 8) graph) :
    ¬ graph.IsAcyclic := by sorry
