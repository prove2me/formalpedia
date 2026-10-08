-- Prove2me | Theorems.Thm_FinitePointComplementBaseCase
-- name    : FinitePointComplementBaseCase
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T20:26:11.203363+00:00
-- url     : https://prove2.me/theorems/3d8b7fd4-b881-4757-8b36-abb8e3a472e8
-- title:
--   Finite Point Complement Base Case
-- statement:
--   [Finite point complement base case]
--   Let $V$ be a finite set of points in the Euclidean plane.  Then
--   $\mathbb R^2\setminus V$ is polygonally path connected.  Moreover
--   $\mathbb R^2\setminus V$ is itself a complement component of $V$, and
--   every complement component of $V$ is equal to $\mathbb R^2\setminus V$.
--
--   **Formalization Note** This node is ported from the Trellis formalization of the crossing lemma and its consequences ([wpegden/crossing-consequences](https://github.com/wpegden/crossing-consequences), commit `8769d142`, W. Pegden, Apache-2.0); the statement is the Trellis node `FinitePointComplementBaseCase`.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/FinitePointComplementBaseCase.lean#L1-L180

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Set.Finite.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Topology.Baire.Lemmas
import Definitions.Def_PlaneFaceData
import Definitions.Def_PolygonallyPathConnected

open Classical
noncomputable section

lemma FinitePointComplementBaseCase
    (V : Finset (EuclideanSpace ℝ (Fin 2))) :
    PolygonallyPathConnected ((V : Set (EuclideanSpace ℝ (Fin 2)))ᶜ) ∧
      ComplementComponent (V : Set (EuclideanSpace ℝ (Fin 2)))
        ((V : Set (EuclideanSpace ℝ (Fin 2)))ᶜ) ∧
        ∀ C : Set (EuclideanSpace ℝ (Fin 2)),
          ComplementComponent (V : Set (EuclideanSpace ℝ (Fin 2))) C →
            C = ((V : Set (EuclideanSpace ℝ (Fin 2)))ᶜ) := by sorry
