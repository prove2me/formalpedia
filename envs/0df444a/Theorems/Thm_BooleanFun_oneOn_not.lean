-- Prove2me | Theorems.Thm_BooleanFun_oneOn_not
-- name    : BooleanFun.oneOn_not
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T18:59:06.506084+00:00
-- url     : https://prove2.me/theorems/9f55ea02-41bd-47b2-97a9-23cf46733a3f
-- title:
--   Boolean Fun: one On not
-- statement:
--   The Boolean Fun construction uses the one On not property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-booleanfun/blob/3a75a656104e18dec6169c3f06f340ed9da43370/BooleanFun/Auxiliary.lean#L104-L105
-- source:
--   https://github.com/roos-j/lean-booleanfun/blob/3a75a656104e18dec6169c3f06f340ed9da43370/BooleanFun/Auxiliary.lean#L104-L105

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

theorem BooleanFun.oneOn_not : oneOn (¬p) = 1 - oneOn p := by sorry
