-- Prove2me | Theorems.Thm_BooleanFun_rw_ite_right
-- name    : BooleanFun.rw_ite_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T18:58:42.489221+00:00
-- url     : https://prove2.me/theorems/3153d681-3609-4660-bb19-4c6e9a221317
-- title:
--   Boolean Fun: rw ite right
-- statement:
--   The Boolean Fun construction uses the rw ite right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-booleanfun/blob/3a75a656104e18dec6169c3f06f340ed9da43370/BooleanFun/Auxiliary.lean#L73-L74
-- source:
--   https://github.com/roos-j/lean-booleanfun/blob/3a75a656104e18dec6169c3f06f340ed9da43370/BooleanFun/Auxiliary.lean#L73-L74

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
variable {α : Sort*} {P : Prop} [Decidable P] {a b c : α}

theorem BooleanFun.rw_ite_right (h : ¬P → a = c):
    ite P b a = ite P b c := by sorry
