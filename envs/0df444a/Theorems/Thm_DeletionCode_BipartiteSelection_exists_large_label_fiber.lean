-- Prove2me | Theorems.Thm_DeletionCode_BipartiteSelection_exists_large_label_fiber
-- name    : DeletionCode.BipartiteSelection.exists_large_label_fiber
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:29:50.463212+00:00
-- url     : https://prove2.me/theorems/b49332e1-8a3a-4917-808e-faafa14b7f6f
-- title:
--   Bipartite Selection: exists large label fiber
-- statement:
--   The finite pigeonhole bound in multiplication form, without rounding.
--   The selected label exists even when I is empty.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/BipartiteSelection.lean#L21-L37
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/BipartiteSelection.lean#L21-L37

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

theorem DeletionCode.BipartiteSelection.exists_large_label_fiber {V : Type*} {Q : ℕ} (I : Finset V)
    (label : V → Fin Q) (hQ : 1 ≤ Q) :
    ∃ a : Fin Q, I.card ≤ Q * (I.filter (fun v => label v = a)).card := by sorry
