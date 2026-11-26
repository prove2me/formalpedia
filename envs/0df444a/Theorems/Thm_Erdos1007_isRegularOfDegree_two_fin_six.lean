-- Prove2me | Theorems.Thm_Erdos1007_isRegularOfDegree_two_fin_six
-- name    : Erdos1007.isRegularOfDegree_two_fin_six
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:53:35.195147+00:00
-- url     : https://prove2.me/theorems/142a8a23-f52a-52f2-94af-c1b5ba114cd3
-- title:
--   Erdos1007: is Regular Of Degree two fin six
-- statement:
--   **Two-regular graphs on six vertices.** A two-regular simple graph on six vertices is
--   isomorphic to the hexagon `C₆` or to the disjoint sum `K₃ ⊔ K₃` of two triangles.
--
--   Blueprint node `lem:two-regular-six`, attributed to Chaffee--Noble. The two neighbours `a` and
--   `b` of `0` are either adjacent, which forces the triangles `{0, a, b}` and its complement, or
--   not, in which case the walk `0, a, c, x, d, b` closes the hexagon. The second disjunct's graph
--   is `SimpleGraph.sum` of two complete graphs on `Fin 3`.
--
--   Source: https://github.com/Dishah3241/Erdos1007/blob/43f89415a6663848a1445effbda8b3abe77b052b/Erdos1007/Combinatorics/SimpleGraph/TwoRegularSix.lean#L88-L495
-- source:
--   https://github.com/Dishah3241/Erdos1007/blob/43f89415a6663848a1445effbda8b3abe77b052b/Erdos1007/Combinatorics/SimpleGraph/TwoRegularSix.lean#L88-L495

module
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Finset.Sort
public import Mathlib.Combinatorics.SimpleGraph.CycleGraph
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Combinatorics.SimpleGraph.Sum
public import Definitions.Def_Erdos1007_Combinatorics_SimpleGraph_TwoRegularSix
set_option autoImplicit false
@[expose] public section
public section
open Erdos1007
open SimpleGraph
variable {G : SimpleGraph (Fin 6)} [DecidableRel G.Adj]
set_option maxHeartbeats 1000000

theorem Erdos1007.isRegularOfDegree_two_fin_six (G : SimpleGraph (Fin 6)) [DecidableRel G.Adj]
    (h : G.IsRegularOfDegree 2) :
    Nonempty (G ≃g SimpleGraph.cycleGraph 6) ∨
      Nonempty (G ≃g (⊤ : SimpleGraph (Fin 3)) ⊕g (⊤ : SimpleGraph (Fin 3))) := by sorry
