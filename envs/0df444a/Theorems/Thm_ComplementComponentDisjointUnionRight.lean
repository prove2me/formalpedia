-- Prove2me | Theorems.Thm_ComplementComponentDisjointUnionRight
-- name    : ComplementComponentDisjointUnionRight
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T20:24:47.260114+00:00
-- url     : https://prove2.me/theorems/62676f5c-d9e3-46e8-a355-1f3b9525bb5c
-- title:
--   Complement Component Disjoint Union Right
-- statement:
--   Let $A,B,C\subseteq\mathbb R^2$.  If $C$ is a complement component of
--   $A$ and $C\cap B=\varnothing$, then $C$ is a complement component of
--   $A\cup B$.
--
--   **Formalization Note** This node is ported from the Trellis formalization of the crossing lemma and its consequences ([wpegden/crossing-consequences](https://github.com/wpegden/crossing-consequences), commit `8769d142`, W. Pegden, Apache-2.0); the statement is the Trellis node `ComplementComponentDisjointUnionRight`.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/ComplementComponentDisjointUnionRight.lean#L1-L24

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Set.Finite.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Definitions.Def_PlaneFaceData

lemma ComplementComponentDisjointUnionRight
    (A B C : Set (EuclideanSpace ℝ (Fin 2))) :
    ComplementComponent A C → Disjoint C B →
      ComplementComponent (A ∪ B) C := by sorry
