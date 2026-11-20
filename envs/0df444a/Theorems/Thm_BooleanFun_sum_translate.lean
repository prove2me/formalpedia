-- Prove2me | Theorems.Thm_BooleanFun_sum_translate
-- name    : BooleanFun.sum_translate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:03:19.687619+00:00
-- url     : https://prove2.me/theorems/9dd773a3-06bf-49d2-aee0-433d0811a394
-- title:
--   Boolean Fun: sum translate
-- statement:
--   Translation invariance
--
--   Source: https://github.com/roos-j/lean-booleanfun/blob/3a75a656104e18dec6169c3f06f340ed9da43370/BooleanFun/Basic.lean#L69-L83
-- source:
--   https://github.com/roos-j/lean-booleanfun/blob/3a75a656104e18dec6169c3f06f340ed9da43370/BooleanFun/Basic.lean#L69-L83

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

theorem BooleanFun.sum_translate (a : Fin n → Fin 2) : ∑ x, f x = ∑ x, f (x + a) := by sorry
