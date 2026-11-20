-- Prove2me | Theorems.Thm_BooleanFun_flipAt_involutive
-- name    : BooleanFun.flipAt_involutive
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:03:36.956093+00:00
-- url     : https://prove2.me/theorems/c404a95e-067b-453c-bbb5-cfb799ebf834
-- title:
--   Boolean Fun: flip At involutive
-- statement:
--   Flipping a bit is an involution on `Fin n → Fin 2`.
--
--   Source: https://github.com/roos-j/lean-booleanfun/blob/3a75a656104e18dec6169c3f06f340ed9da43370/BooleanFun/Basic.lean#L274-L274
-- source:
--   https://github.com/roos-j/lean-booleanfun/blob/3a75a656104e18dec6169c3f06f340ed9da43370/BooleanFun/Basic.lean#L274-L274

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

theorem BooleanFun.flipAt_involutive {i₀ : Fin n} : Function.Involutive (flipAt i₀) := by sorry
