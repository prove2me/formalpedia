-- Prove2me | Theorems.Thm_ComplementComponentAbsorbsConnectedSubset
-- name    : ComplementComponentAbsorbsConnectedSubset
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T20:24:42.942983+00:00
-- url     : https://prove2.me/theorems/078557bc-11c5-4764-8177-4a0334956f90
-- title:
--   Complement Component Absorbs Connected Subset
-- statement:
--   Let $K,C,T\subseteq\mathbb R^2$.  Suppose $C$ is a complement component
--   of $K$, and suppose $T$ is a nonempty connected subset of
--   $\mathbb R^2\setminus K$.  If $C\cap T\neq\varnothing$, then
--   $T\subseteq C$.
--
--   **Formalization Note** This node is ported from the Trellis formalization of the crossing lemma and its consequences ([wpegden/crossing-consequences](https://github.com/wpegden/crossing-consequences), commit `8769d142`, W. Pegden, Apache-2.0); the statement is the Trellis node `ComplementComponentAbsorbsConnectedSubset`.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/ComplementComponentAbsorbsConnectedSubset.lean#L1-L31

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Set.Finite.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Definitions.Def_PlaneFaceData

open Classical
noncomputable section

lemma ComplementComponentAbsorbsConnectedSubset
    (K C T : Set (EuclideanSpace ℝ (Fin 2))) :
    ComplementComponent K C →
      T.Nonempty → T ⊆ Kᶜ → IsConnected T →
        (C ∩ T).Nonempty → T ⊆ C := by sorry
