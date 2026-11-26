-- Prove2me | Theorems.Thm_Erdos1007_completeGraph_five_deleteEdge_unitDistance
-- name    : Erdos1007.completeGraph_five_deleteEdge_unitDistance
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:53:20.141832+00:00
-- url     : https://prove2.me/theorems/62f7b868-666b-58b1-b0c9-6058fc3f1bac
-- title:
--   Erdos1007: complete Graph five delete Edge unit Distance
-- statement:
--   **Upper bound** for the dimension of `K₅ − e`: the complete graph on five vertices with the
--   edge `s(3, 4)` deleted admits a unit-distance representation in `ℝ³` (blueprint node
--   `lem:kn-minus-e`).
--
--   Vertices `0`, `1` and `2` form a unit equilateral triangle, and `3` and `4` are the two apexes of
--   the regular tetrahedra on that triangle. Chaffee–Noble Lemma 2, attributed there to
--   Erdős–Harary–Tutte.
--
--   Source: https://github.com/Dishah3241/Erdos1007/blob/43f89415a6663848a1445effbda8b3abe77b052b/Erdos1007/Geometry/CompleteMinusEdge.lean#L205-L237
-- source:
--   https://github.com/Dishah3241/Erdos1007/blob/43f89415a6663848a1445effbda8b3abe77b052b/Erdos1007/Geometry/CompleteMinusEdge.lean#L205-L237

module
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Definitions.Def_Erdos1007_Geometry_CompleteMinusEdge
set_option autoImplicit false
@[expose] public section
open Erdos1007
noncomputable section
public section

theorem Erdos1007.completeGraph_five_deleteEdge_unitDistance :
    ∃ f : Fin 5 → EuclideanSpace ℝ (Fin 3), Function.Injective f ∧
      ∀ u v, ((⊤ : SimpleGraph (Fin 5)).deleteEdges {s(3, 4)}).Adj u v →
        dist (f u) (f v) = 1 := by sorry
