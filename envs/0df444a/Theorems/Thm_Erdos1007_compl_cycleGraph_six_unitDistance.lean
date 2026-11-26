-- Prove2me | Theorems.Thm_Erdos1007_compl_cycleGraph_six_unitDistance
-- name    : Erdos1007.compl_cycleGraph_six_unitDistance
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:53:58.903466+00:00
-- url     : https://prove2.me/theorems/61263ef1-c95a-4c82-ad92-1008d21c7caf
-- title:
--   Erdos1007: compl cycle Graph six unit Distance
-- statement:
--   The complement of the hexagon admits a unit-distance representation in the plane
--   (blueprint node `lem:prism-planar`).
--
--   The triangles `{0, 2, 4}` and `{1, 3, 5}` are unit equilateral triangles a distance one apart,
--   and the matching between them is vertical. Chaffee–Noble record this placement in the proof of
--   their Theorem 7.
--
--   Source: https://github.com/Dishah3241/Erdos1007/blob/43f89415a6663848a1445effbda8b3abe77b052b/Erdos1007/Geometry/Prism.lean#L137-L179
-- source:
--   https://github.com/Dishah3241/Erdos1007/blob/43f89415a6663848a1445effbda8b3abe77b052b/Erdos1007/Geometry/Prism.lean#L137-L179

module
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.CycleGraph
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import Definitions.Def_Erdos1007_Geometry_Prism
set_option autoImplicit false
@[expose] public section
open Erdos1007
noncomputable section
public section

theorem Erdos1007.compl_cycleGraph_six_unitDistance :
    ∃ f : Fin 6 → EuclideanSpace ℝ (Fin 2), Function.Injective f ∧
      ∀ u v, (SimpleGraph.cycleGraph 6)ᶜ.Adj u v → dist (f u) (f v) = 1 := by sorry
