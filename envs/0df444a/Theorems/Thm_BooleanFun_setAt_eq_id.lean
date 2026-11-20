-- Prove2me | Theorems.Thm_BooleanFun_setAt_eq_id
-- name    : BooleanFun.setAt_eq_id
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:04:32.57527+00:00
-- url     : https://prove2.me/theorems/7cee32b7-83ce-481c-b86b-589e56d49877
-- title:
--   Boolean Fun: set At eq id
-- statement:
--   The Boolean Fun construction uses the set At eq id property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-booleanfun/blob/3a75a656104e18dec6169c3f06f340ed9da43370/BooleanFun/Basic.lean#L405-L410
-- source:
--   https://github.com/roos-j/lean-booleanfun/blob/3a75a656104e18dec6169c3f06f340ed9da43370/BooleanFun/Basic.lean#L405-L410

import Definitions.Def_BooleanFun_Auxiliary
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.CharP.Pi
import Definitions.Def_BooleanFun_Basic
set_option autoImplicit false
open BooleanFun
open Real BigOperators Function Finset Pi
open RealInnerProductSpace
noncomputable section
variable {α : Type*}
variable {n : ℕ} {f g : BooleanFunc n} {x y : Fin n → Fin 2} {i : Fin n}
variable {S S' : Finset (Fin n)} {v : Fin 2}

theorem BooleanFun.setAt_eq_id (h : x i = v) : setAt i v x = x := by sorry
