-- Prove2me | Theorems.Thm_FinitePolygonalSetComplementComponents
-- name    : FinitePolygonalSetComplementComponents
-- status  : Open
-- author  : @moona3k
-- created : 2026-10-04T21:03:56.385011+00:00
-- url     : https://prove2.me/theorems/1e8bdada-bbc5-4508-a537-75f7e5e9d49e
-- title:
--   Finite Polygonal Set Complement Components
-- statement:
--   Let $K$ be a finite polygonal set in the plane.  The connected components of
--   $\mathbb R^2\setminus K$ are indexed by a finite type of faces.  More
--   precisely, there are a finite type $\mathcal F$ and sets
--   $\operatorname{faceSet}(F)\subseteq\mathbb R^2$, $F\in\mathcal F$, such
--   that each listed set is a complement component of $K$, every complement
--   component is listed exactly once, and every point of $K^c$ lies in exactly
--   one listed set.
--
--   **Formalization Note** This node is ported from the Trellis formalization of the crossing lemma and its consequences ([wpegden/crossing-consequences](https://github.com/wpegden/crossing-consequences), commit `8769d142`, W. Pegden, Apache-2.0); the statement is the Trellis node `FinitePolygonalSetComplementComponents`.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/FinitePolygonalSetComplementComponents.lean#L1-L158

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Set.Finite.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Topology.Baire.Lemmas
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Normed.Affine.AddTorsor
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.Convex.Between
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.Order.IntermediateValue
import Definitions.Def_FinitePolygonalSet
import Definitions.Def_PlaneFaceData

open Classical
noncomputable section

lemma FinitePolygonalSetComplementComponents (K : FinitePolygonalSet) :
    ∃ Face : Type, ∃ _ : Fintype Face,
      ∃ faceSet : Face → Set (EuclideanSpace ℝ (Fin 2)),
        (∀ F : Face, ComplementComponent K.carrier (faceSet F)) ∧
          (∀ C : Set (EuclideanSpace ℝ (Fin 2)),
            ComplementComponent K.carrier C → ∃! F : Face, faceSet F = C) ∧
          (∀ p : EuclideanSpace ℝ (Fin 2),
            p ∈ K.carrierᶜ → ∃! F : Face, p ∈ faceSet F) := by sorry
