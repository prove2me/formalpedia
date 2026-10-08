-- Prove2me | Theorems.Thm_ConnectedSubsetContainedInUniqueComplementComponent
-- name    : ConnectedSubsetContainedInUniqueComplementComponent
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T20:24:55.691991+00:00
-- url     : https://prove2.me/theorems/92fb8a21-2204-406c-b58a-a1c57047126a
-- title:
--   Connected Subset Contained In Unique Complement Component
-- statement:
--   Let $K,T\subseteq\mathbb R^2$.  If $T$ is nonempty, connected, and
--   contained in $\mathbb R^2\setminus K$, then there is a unique complement
--   component of $K$ that contains $T$.
--
--   **Formalization Note** This node is ported from the Trellis formalization of the crossing lemma and its consequences ([wpegden/crossing-consequences](https://github.com/wpegden/crossing-consequences), commit `8769d142`, W. Pegden, Apache-2.0); the statement is the Trellis node `ConnectedSubsetContainedInUniqueComplementComponent`.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/ConnectedSubsetContainedInUniqueComplementComponent.lean#L1-L34

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Set.Finite.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Definitions.Def_PlaneFaceData

open Classical
noncomputable section

lemma ConnectedSubsetContainedInUniqueComplementComponent
    (K T : Set (EuclideanSpace ℝ (Fin 2)))
    (hTne : T.Nonempty) (hTK : T ⊆ Kᶜ) (hTconn : IsConnected T) :
    ∃! C : Set (EuclideanSpace ℝ (Fin 2)), ComplementComponent K C ∧ T ⊆ C := by sorry
