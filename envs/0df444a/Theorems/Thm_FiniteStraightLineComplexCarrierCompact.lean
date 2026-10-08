-- Prove2me | Theorems.Thm_FiniteStraightLineComplexCarrierCompact
-- name    : FiniteStraightLineComplexCarrierCompact
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T20:26:21.355977+00:00
-- url     : https://prove2.me/theorems/d849c4a9-23df-48f6-b37f-7da717db5962
-- title:
--   Finite Straight Line Complex Carrier Compact
-- statement:
--   Let $A\subseteq\mathbb R^2$ be written as
--   $$
--     A=V\cup\bigcup_{e\in E} [e_1,e_2],
--   $$
--   where $V$ is a finite set of points and $E$ is a finite set of ordered
--   endpoint pairs.  Then $A$ is compact.
--
--   **Formalization Note** This node is ported from the Trellis formalization of the crossing lemma and its consequences ([wpegden/crossing-consequences](https://github.com/wpegden/crossing-consequences), commit `8769d142`, W. Pegden, Apache-2.0); the statement is the Trellis node `FiniteStraightLineComplexCarrierCompact`.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/FiniteStraightLineComplexCarrierCompact.lean#L1-L23

import Mathlib.Tactic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Set.Finite.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic

open Classical
noncomputable section

lemma FiniteStraightLineComplexCarrierCompact
    (A : Set (EuclideanSpace ℝ (Fin 2)))
    (V : Finset (EuclideanSpace ℝ (Fin 2)))
    (E : Finset (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)))
    (hA :
      A =
        (V : Set (EuclideanSpace ℝ (Fin 2))) ∪
          ⋃ e : {e // e ∈ E}, segment ℝ e.1.1 e.1.2) :
    IsCompact A := by sorry
