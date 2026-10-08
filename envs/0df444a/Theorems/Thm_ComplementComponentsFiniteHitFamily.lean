-- Prove2me | Theorems.Thm_ComplementComponentsFiniteHitFamily
-- name    : ComplementComponentsFiniteHitFamily
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T20:24:54.921841+00:00
-- url     : https://prove2.me/theorems/c02435e7-073c-4335-8ee6-016e62982d51
-- title:
--   Complement Components Finite Hit Family
-- statement:
--   Let $K\subseteq\mathbb R^2$, let $I$ be a finite type, and let
--   $\{P_i\}_{i\in I}$ be a finite family of nonempty connected subsets of
--   $\mathbb R^2\setminus K$.  Suppose that every complement component of $K$
--   meets at least one $P_i$.  Then there is a finite set $\mathcal C$ of
--   subsets of the plane such that every member of $\mathcal C$ is a complement
--   component of $K$, and every complement component of $K$ belongs to
--   $\mathcal C$.
--
--   **Formalization Note** This node is ported from the Trellis formalization of the crossing lemma and its consequences ([wpegden/crossing-consequences](https://github.com/wpegden/crossing-consequences), commit `8769d142`, W. Pegden, Apache-2.0); the statement is the Trellis node `ComplementComponentsFiniteHitFamily`.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/ComplementComponentsFiniteHitFamily.lean#L1-L68

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Set.Finite.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Definitions.Def_PlaneFaceData

open Classical
noncomputable section

lemma ComplementComponentsFiniteHitFamily
    (K : Set (EuclideanSpace ℝ (Fin 2))) {ι : Type} [Fintype ι]
    (P : ι → Set (EuclideanSpace ℝ (Fin 2)))
    (hPne : ∀ i, (P i).Nonempty)
    (hPsub : ∀ i, P i ⊆ Kᶜ)
    (hPconn : ∀ i, IsConnected (P i))
    (hhit : ∀ C : Set (EuclideanSpace ℝ (Fin 2)),
      ComplementComponent K C → ∃ i, (C ∩ P i).Nonempty) :
    ∃ comps : Finset (Set (EuclideanSpace ℝ (Fin 2))),
      (∀ C ∈ comps, ComplementComponent K C) ∧
        ∀ C : Set (EuclideanSpace ℝ (Fin 2)),
          ComplementComponent K C → C ∈ comps := by sorry
