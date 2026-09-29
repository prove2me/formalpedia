-- Prove2me | Theorems.Thm_Erdos180_thetaCopy_base_center_color_eq
-- name    : Erdos180.thetaCopy_base_center_color_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-04T02:11:57.030295+00:00
-- url     : https://prove2.me/theorems/14553a58-0bf5-4371-a477-e80ce40f0d5d
-- title:
--   Bases and centres of a theta copy share a colour
-- statement:
--   In a two-colouring of a graph containing a copy of the theta graph $S_2$, every base and
--   every centre of that copy receive the same colour.
--
--   Bases and centres are the original vertices of $K_{3,2}$ and lie at even distance from one
--   another, hence on the same side of the bipartition. This is the colour bookkeeping behind
--   Definition 2.2(1), the requirement that admissible identifications preserve colours and hence
--   keep the quotient bipartite.
-- source:
--   https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/CompactnessAndDegeneracy.lean#L4683-L4693

import Definitions.Def_erdos180_core4
import Mathlib.Combinatorics.SimpleGraph.Coloring.VertexColoring

open Erdos180
open Finset SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] [DecidableEq V] in
theorem Erdos180.thetaCopy_base_center_color_eq
    {G : SimpleGraph V}
    (color : G.Coloring (Fin 2))
    (copy : SimpleGraph.Copy thetaGraph G)
    (base : Fin 3) (center : Fin 2) :
    color (copy (.inl (.inl base))) =
      color (copy (.inl (.inr center))) := by sorry
