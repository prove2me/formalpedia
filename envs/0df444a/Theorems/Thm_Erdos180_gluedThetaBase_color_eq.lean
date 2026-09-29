-- Prove2me | Theorems.Thm_Erdos180_gluedThetaBase_color_eq
-- name    : Erdos180.gluedThetaBase_color_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-04T02:12:16.528822+00:00
-- url     : https://prove2.me/theorems/e0d6093a-c2d3-47e5-9605-71119ca6efd8
-- title:
--   Gluing two theta copies preserves the colour class
-- statement:
--   If two copies of the theta graph are glued by identifying one base of the second with one
--   base of the first, then all bases of both copies carry the colour of the first copy's initial
--   base.
--
--   This is the colour consistency of the template $J_0$, which is built from two copies of $S_2$
--   with base triples $\{x,y,z\}$ and $\{x',y,z\}$ identified along $y$ and $z$ (Definition 2.3).
--   It is what makes $J_0$ properly two-coloured, so that its admissible quotients are bipartite.
-- source:
--   https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/CompactnessAndDegeneracy.lean#L4710-L4730

import Definitions.Def_erdos180_core4
import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.Combinatorics.SimpleGraph.Coloring.VertexColoring

open Erdos180
open Finset SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] [DecidableEq V] in
theorem Erdos180.gluedThetaBase_color_eq
    {G : SimpleGraph V}
    (copies : Fin 2 → SimpleGraph.Copy thetaGraph G)
    (hfirst :
      copies 1 (.inl (.inl (1 : Fin 3))) =
        copies 0 (.inl (.inl (1 : Fin 3))))
    (color : G.Coloring (Fin 2))
    (copy : Fin 2) (base : Fin 3) :
    color (copies copy (.inl (.inl base))) =
      color (copies 0 (.inl (.inl (0 : Fin 3)))) := by sorry
