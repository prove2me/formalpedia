-- Prove2me | Theorems.Thm_DeletionCode_FiniteConflictGraph_vertex_unique
-- name    : DeletionCode.FiniteConflictGraph.vertex_unique
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:34:43.673971+00:00
-- url     : https://prove2.me/theorems/60ccf54b-d4db-4b5f-b7a5-9e2d2724e6e1
-- title:
--   Finite Conflict Graph: vertex unique
-- statement:
--   The Finite Conflict Graph construction uses the vertex unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/FiniteConflictGraph.lean#L76-L77
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/FiniteConflictGraph.lean#L76-L77

import Definitions.Def_DeletionCode_AlignmentTrace
import Definitions.Def_DeletionCode_BoundedWitnessWalk
import Mathlib.Combinatorics.SimpleGraph.Basic
import Definitions.Def_DeletionCode_FiniteConflictGraph
set_option autoImplicit true
open DeletionCode DeletionCode.FiniteConflictGraph
open HeaderRecovery AlignmentTrace EditAlignment
variable {n : ℕ} {H : Type*}

theorem DeletionCode.FiniteConflictGraph.vertex_unique {t k : ℕ} {label : Bits n → H} (x : Vertex t k label) :
    Windows.KUnique (padBits x.val) n k := by sorry
