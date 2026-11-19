-- Prove2me | Theorems.Thm_DeletionCode_ComponentFibers_singleton_fiber_count_bound
-- name    : DeletionCode.ComponentFibers.singleton_fiber_count_bound
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-19T05:24:32.052922+00:00
-- url     : https://prove2.me/theorems/1ad22885-1959-4ecc-affe-80747df5c8c1
-- title:
--   Component Fibers: singleton fiber count bound
-- statement:
--   Non-singleton components use at least two occurrences; surjectivity rules
--   out empty fibers, rather than assuming this lower bound on the count.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/ComponentFibers.lean#L68-L93
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/ComponentFibers.lean#L68-L93

import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.SetTheory.Cardinal.Finite
import Lean.Elab.Tactic.Omega
import Definitions.Def_DeletionCode_ComponentFibers
set_option autoImplicit true
open DeletionCode DeletionCode.ComponentFibers
open scoped BigOperators

theorem DeletionCode.ComponentFibers.singleton_fiber_count_bound {A C : Type*} [Fintype A] [Fintype C]
    (f : A → C) (hsurj : Function.Surjective f) :
    2 * Fintype.card C ≤ Fintype.card A + Fintype.card {c : C // SingletonFiber f c} := by sorry
