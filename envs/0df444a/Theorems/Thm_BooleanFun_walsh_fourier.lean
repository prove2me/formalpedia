-- Prove2me | Theorems.Thm_BooleanFun_walsh_fourier
-- name    : BooleanFun.walsh_fourier
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:02:58.088058+00:00
-- url     : https://prove2.me/theorems/a6c099aa-45de-4ae4-a3b0-13b4ee000d31
-- title:
--   Boolean Fun: walsh fourier
-- statement:
--   Walsh-Fourier expansion : Every Boolean function is equal to a linear combination of Walsh characters.
--
--   Source: https://github.com/roos-j/lean-booleanfun/blob/3a75a656104e18dec6169c3f06f340ed9da43370/BooleanFun/Basic.lean#L332-L333
-- source:
--   https://github.com/roos-j/lean-booleanfun/blob/3a75a656104e18dec6169c3f06f340ed9da43370/BooleanFun/Basic.lean#L332-L333

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

theorem BooleanFun.walsh_fourier (f : BooleanFunc n) : f = ∑ S : Finset (Fin n), (𝓕 f S)•χ S := by sorry
