-- Prove2me | Theorems.Thm_BooleanFun_ite_ite_same
-- name    : BooleanFun.ite_ite_same
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T18:58:40.879639+00:00
-- url     : https://prove2.me/theorems/ed7f9791-9467-46b3-b9cd-72a2353067de
-- title:
--   Boolean Fun: ite ite same
-- statement:
--   The Boolean Fun construction uses the ite ite same property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-booleanfun/blob/3a75a656104e18dec6169c3f06f340ed9da43370/BooleanFun/Auxiliary.lean#L67-L68
-- source:
--   https://github.com/roos-j/lean-booleanfun/blob/3a75a656104e18dec6169c3f06f340ed9da43370/BooleanFun/Auxiliary.lean#L67-L68

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

theorem BooleanFun.ite_ite_same (a b c : α):
    ite P (ite P a b) c = ite P a c := by sorry
