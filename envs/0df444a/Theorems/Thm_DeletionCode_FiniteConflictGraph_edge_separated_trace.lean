-- Prove2me | Theorems.Thm_DeletionCode_FiniteConflictGraph_edge_separated_trace
-- name    : DeletionCode.FiniteConflictGraph.edge_separated_trace
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:35:00.01146+00:00
-- url     : https://prove2.me/theorems/9b7d889e-b9b5-4b9f-a0c7-5851d01a8e7b
-- title:
--   Finite Conflict Graph: edge separated trace
-- statement:
--   Every oriented edge supplies a genuine separated full-size trace.
--   The exact counters and separation follow from exceptional-set exclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/FiniteConflictGraph.lean#L104-L115
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/FiniteConflictGraph.lean#L104-L115

import Definitions.Def_DeletionCode_AlignmentTrace
import Definitions.Def_DeletionCode_BoundedWitnessWalk
import Mathlib.Combinatorics.SimpleGraph.Basic
import Definitions.Def_DeletionCode_FiniteConflictGraph
set_option autoImplicit true
open DeletionCode DeletionCode.FiniteConflictGraph
open HeaderRecovery AlignmentTrace EditAlignment
variable {n : ℕ} {H : Type*}

theorem DeletionCode.FiniteConflictGraph.edge_separated_trace {t k : ℕ} {label : Bits n → H}
    {x y : Vertex t k label} (hxy : (graph t k label).Adj x y) :
    ∃ trace : Trace,
      trace.source = List.ofFn x.val ∧ trace.target = List.ofFn y.val ∧
      trace.deletions = t ∧ trace.insertions = t ∧
      Separated (4 * windowLength k) trace := by sorry
