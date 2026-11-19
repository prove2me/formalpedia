-- Prove2me | Theorems.Thm_DeletionCode_BipartiteSelection_componentColor_valid
-- name    : DeletionCode.BipartiteSelection.componentColor_valid
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-19T05:48:06.475922+00:00
-- url     : https://prove2.me/theorems/fdb6c6ff-9646-4ba4-8d4d-3a670600ef9a
-- title:
--   Bipartite Selection: component Color valid
-- statement:
--   The Bipartite Selection construction uses the component Color valid property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/BipartiteSelection.lean#L50-L54
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/BipartiteSelection.lean#L50-L54

import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Lean.Elab.Tactic.Omega
import Definitions.Def_DeletionCode_BipartiteSelection
set_option autoImplicit true
open DeletionCode DeletionCode.BipartiteSelection
open SimpleGraph
open scoped BigOperators
variable {V : Type*} (G : SimpleGraph V)

theorem DeletionCode.BipartiteSelection.componentColor_valid (C : G.ConnectedComponent) (hC : C.toSimpleGraph.Colorable 2)
    {v w : C} (hvw : C.toSimpleGraph.Adj v w) :
    componentColor G C v ≠ componentColor G C w := by sorry
