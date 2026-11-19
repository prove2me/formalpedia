-- Prove2me | Theorems.Thm_DeletionCode_BipartiteSelection_mem_goodVertices
-- name    : DeletionCode.BipartiteSelection.mem_goodVertices
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:48:32.264179+00:00
-- url     : https://prove2.me/theorems/90443d46-6690-4158-a2b1-ec93c95809c7
-- title:
--   Bipartite Selection: mem good Vertices
-- statement:
--   The Bipartite Selection construction uses the mem good Vertices property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/BipartiteSelection.lean#L89-L91
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/BipartiteSelection.lean#L89-L91

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
variable [Fintype V]

theorem DeletionCode.BipartiteSelection.mem_goodVertices (v : V) : v ∈ goodVertices G ↔ Good G v := by sorry
