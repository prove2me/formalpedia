-- Prove2me | Theorems.Thm_BooleanFun_oneOn_and
-- name    : BooleanFun.oneOn_and
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T18:59:04.382633+00:00
-- url     : https://prove2.me/theorems/8945aa5f-3d0c-4f7c-97a7-73ea72c94424
-- title:
--   Boolean Fun: one On and
-- statement:
--   The Boolean Fun construction uses the one On and property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-booleanfun/blob/3a75a656104e18dec6169c3f06f340ed9da43370/BooleanFun/Auxiliary.lean#L101-L102
-- source:
--   https://github.com/roos-j/lean-booleanfun/blob/3a75a656104e18dec6169c3f06f340ed9da43370/BooleanFun/Auxiliary.lean#L101-L102

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Analysis.Real.Sqrt
import Definitions.Def_BooleanFun_Auxiliary
set_option autoImplicit false
open BooleanFun
open Finset Pi
variable {α : Type*} {β : Type*}
variable {s : Finset α}
variable {ι : Type*} [Fintype ι]
variable {κ : Type*}
variable {R : Type*} {M : Type*}
variable [Ring R] [AddCommGroup M] [Module R M]
noncomputable section
variable {p q : Prop}
open Classical

theorem BooleanFun.oneOn_and : oneOn (p ∧ q) = (oneOn p) * (oneOn q) := by sorry
