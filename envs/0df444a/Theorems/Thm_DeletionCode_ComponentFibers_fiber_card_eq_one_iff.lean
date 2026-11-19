-- Prove2me | Theorems.Thm_DeletionCode_ComponentFibers_fiber_card_eq_one_iff
-- name    : DeletionCode.ComponentFibers.fiber_card_eq_one_iff
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-19T05:24:22.858566+00:00
-- url     : https://prove2.me/theorems/e5479d73-3699-4337-be9a-7fa4758841e2
-- title:
--   Component Fibers: fiber card eq one iff
-- statement:
--   The witness-based definition agrees with the cardinality of the actual fiber.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/ComponentFibers.lean#L36-L56
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/ComponentFibers.lean#L36-L56

import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.SetTheory.Cardinal.Finite
import Lean.Elab.Tactic.Omega
import Definitions.Def_DeletionCode_ComponentFibers
set_option autoImplicit true
open DeletionCode DeletionCode.ComponentFibers
open scoped BigOperators

theorem DeletionCode.ComponentFibers.fiber_card_eq_one_iff {A C : Type*} [Fintype A] (f : A → C) (c : C) :
    (fiber f c).card = 1 ↔ SingletonFiber f c := by sorry
