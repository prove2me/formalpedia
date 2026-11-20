-- Prove2me | Theorems.Thm_BooleanFun_walsh_plancherel
-- name    : BooleanFun.walsh_plancherel
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:03:49.212856+00:00
-- url     : https://prove2.me/theorems/ead6e9b0-495a-456b-8247-a7d987c80db8
-- title:
--   Boolean Fun: walsh plancherel
-- statement:
--   Plancherel/Parseval theorem for Boolean functions.
--
--   Source: https://github.com/roos-j/lean-booleanfun/blob/3a75a656104e18dec6169c3f06f340ed9da43370/BooleanFun/Basic.lean#L347-L348
-- source:
--   https://github.com/roos-j/lean-booleanfun/blob/3a75a656104e18dec6169c3f06f340ed9da43370/BooleanFun/Basic.lean#L347-L348

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

theorem BooleanFun.walsh_plancherel : ‖f‖^2 = ∑ S : Finset (Fin n), |𝓕 f S|^2 := by sorry
