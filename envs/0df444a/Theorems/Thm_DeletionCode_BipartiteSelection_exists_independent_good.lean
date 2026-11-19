-- Prove2me | Theorems.Thm_DeletionCode_BipartiteSelection_exists_independent_good
-- name    : DeletionCode.BipartiteSelection.exists_independent_good
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-19T05:48:34.23216+00:00
-- url     : https://prove2.me/theorems/a48681a4-ecfc-4003-8d48-dc4961a2c172
-- title:
--   Bipartite Selection: exists independent good
-- statement:
--   At least half of all vertices in bipartite components can be selected
--   as one independent set. Component colorings and the large fiber are derived.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/BipartiteSelection.lean#L95-L107
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/BipartiteSelection.lean#L95-L107

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

theorem DeletionCode.BipartiteSelection.exists_independent_good :
    ∃ I : Finset V, (∀ v ∈ I, Good G v) ∧ G.IsIndepSet (I : Set V) ∧
      (goodVertices G).card ≤ 2 * I.card := by sorry
