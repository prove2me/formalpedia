-- Prove2me | Theorems.Thm_BooleanFun_dderiv_walsh
-- name    : BooleanFun.dderiv_walsh
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:03:07.033174+00:00
-- url     : https://prove2.me/theorems/f5da0290-ae2f-4ed9-9bee-1b5c3a0785b5
-- title:
--   Boolean Fun: dderiv walsh
-- statement:
--   The Boolean Fun construction uses the dderiv walsh property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-booleanfun/blob/3a75a656104e18dec6169c3f06f340ed9da43370/BooleanFun/Basic.lean#L386-L390
-- source:
--   https://github.com/roos-j/lean-booleanfun/blob/3a75a656104e18dec6169c3f06f340ed9da43370/BooleanFun/Basic.lean#L386-L390

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

theorem BooleanFun.dderiv_walsh (i : Fin n) (S : Finset (Fin n)) : dderiv i (χ S) = ite (i ∈ S) (χ (S \ {i})) 0 := by sorry
