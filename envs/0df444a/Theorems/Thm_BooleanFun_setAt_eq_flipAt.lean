-- Prove2me | Theorems.Thm_BooleanFun_setAt_eq_flipAt
-- name    : BooleanFun.setAt_eq_flipAt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:04:33.335043+00:00
-- url     : https://prove2.me/theorems/d725add3-5548-4a66-8aa8-d480cec97ee2
-- title:
--   Boolean Fun: set At eq flip At
-- statement:
--   The Boolean Fun construction uses the set At eq flip At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-booleanfun/blob/3a75a656104e18dec6169c3f06f340ed9da43370/BooleanFun/Basic.lean#L412-L417
-- source:
--   https://github.com/roos-j/lean-booleanfun/blob/3a75a656104e18dec6169c3f06f340ed9da43370/BooleanFun/Basic.lean#L412-L417

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

theorem BooleanFun.setAt_eq_flipAt (h : x i ≠ v) : setAt i v x = flipAt i x := by sorry
