-- Prove2me | Theorems.Thm_BooleanFun_walsh_add
-- name    : BooleanFun.walsh_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:03:20.7776+00:00
-- url     : https://prove2.me/theorems/4d3780ea-404c-49bf-adbc-fb9d64d6bb67
-- title:
--   Boolean Fun: walsh add
-- statement:
--   Walsh characters are characters.
--
--   Source: https://github.com/roos-j/lean-booleanfun/blob/3a75a656104e18dec6169c3f06f340ed9da43370/BooleanFun/Basic.lean#L118-L124
-- source:
--   https://github.com/roos-j/lean-booleanfun/blob/3a75a656104e18dec6169c3f06f340ed9da43370/BooleanFun/Basic.lean#L118-L124

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

theorem BooleanFun.walsh_add : χ S (x + y) = (χ S x) * (χ S y) := by sorry
