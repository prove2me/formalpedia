-- Prove2me | Theorems.Thm_DeletionCode_FinitePairUnion_ordered_pair_union_bound
-- name    : DeletionCode.FinitePairUnion.ordered_pair_union_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:41:20.078742+00:00
-- url     : https://prove2.me/theorems/f17c15d9-fb18-4eac-b131-b7c7cd927144
-- title:
--   Finite Pair Union: ordered pair union bound
-- statement:
--   A union of events indexed by a < b has at most choose n 2 times the
--   maximum event size. The counted set contains each outcome only once.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/FinitePairUnion.lean#L38-L58
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/FinitePairUnion.lean#L38-L58

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Choose.Basic
import Definitions.Def_DeletionCode_FinitePairUnion
set_option autoImplicit true
open DeletionCode DeletionCode.FinitePairUnion
open scoped BigOperators
open Finset
noncomputable section
attribute [local instance] Classical.propDecidable

theorem DeletionCode.FinitePairUnion.ordered_pair_union_bound {α : Type*} [Fintype α] [DecidableEq α]
    (n M : ℕ) (P : Fin n → Fin n → α → Prop)
    (hcount : ∀ a b, a < b → (univ.filter (P a b)).card ≤ M) :
    (univ.filter (fun x => ∃ a b, a < b ∧ P a b x)).card ≤ n.choose 2 * M := by sorry
