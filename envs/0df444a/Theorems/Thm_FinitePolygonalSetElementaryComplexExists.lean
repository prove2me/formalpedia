-- Prove2me | Theorems.Thm_FinitePolygonalSetElementaryComplexExists
-- name    : FinitePolygonalSetElementaryComplexExists
-- status  : Open
-- author  : @moona3k
-- created : 2026-10-04T21:03:44.738109+00:00
-- url     : https://prove2.me/theorems/46d000fa-81a0-448a-bdfb-d8bf56f83032
-- title:
--   Finite Polygonal Set Elementary Complex Exists
-- statement:
--   Every finite polygonal set $K$ has an elementary complex refinement in the
--   sense of `FinitePolygonalSetElementaryComplex`.
--
--   **Formalization Note** This node is ported from the Trellis formalization of the crossing lemma and its consequences ([wpegden/crossing-consequences](https://github.com/wpegden/crossing-consequences), commit `8769d142`, W. Pegden, Apache-2.0); the statement is the Trellis node `FinitePolygonalSetElementaryComplexExists`.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/FinitePolygonalSetElementaryComplexExists.lean#L1-L340

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Set.Finite.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic
import Definitions.Def_FinitePolygonalSet
import Definitions.Def_FinitePolygonalSetElementaryComplex

open Classical
noncomputable section

lemma FinitePolygonalSetElementaryComplexExists (K : FinitePolygonalSet) :
    Nonempty (FinitePolygonalSetElementaryComplex K) := by sorry
