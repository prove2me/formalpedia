-- Prove2me | Theorems.Thm_BooleanFun_variance_le_totalInfluence
-- name    : BooleanFun.variance_le_totalInfluence
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:09:35.203999+00:00
-- url     : https://prove2.me/theorems/effdc27e-f31b-4a86-bd6b-7b08036330c8
-- title:
--   Boolean Fun: variance le total Influence
-- statement:
--   L² Poincaré inequality : variance of a Boolean function is ≤ total Influence.
--   See [odonnell2014], Sec. 2.3.
--
--   Source: https://github.com/roos-j/lean-booleanfun/blob/3a75a656104e18dec6169c3f06f340ed9da43370/BooleanFun/Basic.lean#L493-L503
-- source:
--   https://github.com/roos-j/lean-booleanfun/blob/3a75a656104e18dec6169c3f06f340ed9da43370/BooleanFun/Basic.lean#L493-L503

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

theorem BooleanFun.variance_le_totalInfluence (f : BooleanFunc n) : variance f ≤ totalInfluence f := by sorry
