-- Prove2me | Theorems.Thm_BooleanFun_flipAt_bijective
-- name    : BooleanFun.flipAt_bijective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:08:46.524673+00:00
-- url     : https://prove2.me/theorems/1fc32c1d-7956-4a52-951c-dbc0395c91c0
-- title:
--   Boolean Fun: flip At bijective
-- statement:
--   Flipping a bit is a bijection on `Fin n → Fin 2`.
--
--   Source: https://github.com/roos-j/lean-booleanfun/blob/3a75a656104e18dec6169c3f06f340ed9da43370/BooleanFun/Basic.lean#L277-L278
-- source:
--   https://github.com/roos-j/lean-booleanfun/blob/3a75a656104e18dec6169c3f06f340ed9da43370/BooleanFun/Basic.lean#L277-L278

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

theorem BooleanFun.flipAt_bijective {i₀ : Fin n} : Function.Bijective (flipAt i₀) := by sorry
