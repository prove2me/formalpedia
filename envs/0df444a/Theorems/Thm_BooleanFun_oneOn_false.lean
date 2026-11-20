-- Prove2me | Theorems.Thm_BooleanFun_oneOn_false
-- name    : BooleanFun.oneOn_false
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T18:59:04.323088+00:00
-- url     : https://prove2.me/theorems/80c4a457-48b9-4f35-97c3-e3345b55ce99
-- title:
--   Boolean Fun: one On false
-- statement:
--   The Boolean Fun construction uses the one On false property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-booleanfun/blob/3a75a656104e18dec6169c3f06f340ed9da43370/BooleanFun/Auxiliary.lean#L99-L99
-- source:
--   https://github.com/roos-j/lean-booleanfun/blob/3a75a656104e18dec6169c3f06f340ed9da43370/BooleanFun/Auxiliary.lean#L99-L99

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

theorem BooleanFun.oneOn_false (h : ¬p) : oneOn p = 0 := by sorry
