-- Prove2me | Theorems.Thm_DeletionCode_FiniteConnectedGrowth_connected_count_bound
-- name    : DeletionCode.FiniteConnectedGrowth.connected_count_bound
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-19T05:23:46.69884+00:00
-- url     : https://prove2.me/theorems/80bdaffe-8336-46c6-947e-ce393ac92b39
-- title:
--   Finite Connected Growth: connected count bound
-- statement:
--   One saved unit at every connected addition gives the usual (d-1)|B|+1 bound.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/FiniteConnectedGrowth.lean#L77-L93
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/FiniteConnectedGrowth.lean#L77-L93

import Mathlib.Data.Finset.Card
import Mathlib.Logic.Relation
import Lean.Elab.Tactic.Omega
import Definitions.Def_DeletionCode_FiniteConnectedGrowth
set_option autoImplicit true
open DeletionCode DeletionCode.FiniteConnectedGrowth
variable {α : Type*} [DecidableEq α]

theorem DeletionCode.FiniteConnectedGrowth.connected_count_bound (B : Finset α) (r : α → α → Prop)
    (hB : B.Nonempty)
    (hconnected : ∀ a ∈ B, ∀ b ∈ B, Relation.EqvGen (Induced B r) a b)
    (f : Finset α → ℕ) (d : ℕ) (hd : 1 ≤ d)
    (hsingleton : ∀ a ∈ B, f {a} ≤ d)
    (hgrowth : ∀ U : Finset α, U ⊆ B → ∀ w ∈ B, w ∉ U →
      (∃ u ∈ U, r w u ∨ r u w) → f (insert w U) + 1 ≤ f U + d) :
    f B ≤ (d - 1) * B.card + 1 := by sorry
