-- Prove2me | Theorems.Thm_BooleanFun_setAt_other
-- name    : BooleanFun.setAt_other
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:04:00.948387+00:00
-- url     : https://prove2.me/theorems/365fd982-a9d1-4e7a-bc83-14a02e245e1c
-- title:
--   Boolean Fun: set At other
-- statement:
--   Bits other than the `i₀`th bit are unaffected by `setAt`.
--
--   Source: https://github.com/roos-j/lean-booleanfun/blob/3a75a656104e18dec6169c3f06f340ed9da43370/BooleanFun/Basic.lean#L361-L362
-- source:
--   https://github.com/roos-j/lean-booleanfun/blob/3a75a656104e18dec6169c3f06f340ed9da43370/BooleanFun/Basic.lean#L361-L362

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

theorem BooleanFun.setAt_other (i₀ : Fin n) (v : Fin 2) (x : Fin n → Fin 2) (i : Fin n) (h : i₀ ≠ i) : setAt i₀ v x i = x i := by sorry
