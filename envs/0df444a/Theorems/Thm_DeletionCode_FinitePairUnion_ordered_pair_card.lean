-- Prove2me | Theorems.Thm_DeletionCode_FinitePairUnion_ordered_pair_card
-- name    : DeletionCode.FinitePairUnion.ordered_pair_card
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-19T05:41:13.065763+00:00
-- url     : https://prove2.me/theorems/28cd0241-f798-407d-bc57-8ed4b7ab915a
-- title:
--   Finite Pair Union: ordered pair card
-- statement:
--   The number of pairs a < b among n positions is exactly choose n 2,
--   including the empty cases n = 0 and n = 1.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/FinitePairUnion.lean#L31-L34
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/FinitePairUnion.lean#L31-L34

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

theorem DeletionCode.FinitePairUnion.ordered_pair_card (n : ℕ) : Fintype.card (OrderedPair n) = n.choose 2 := by sorry
