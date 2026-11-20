-- Prove2me | Theorems.Thm_BooleanFun_multiplier_walsh
-- name    : BooleanFun.multiplier_walsh
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:05:46.189621+00:00
-- url     : https://prove2.me/theorems/420fdeec-0805-4596-b53d-59d5211e20d1
-- title:
--   Boolean Fun: multiplier walsh
-- statement:
--   Walsh characters are eigenfunctions of multipliers.
--
--   Source: https://github.com/roos-j/lean-booleanfun/blob/3a75a656104e18dec6169c3f06f340ed9da43370/BooleanFun/Basic.lean#L594-L598
-- source:
--   https://github.com/roos-j/lean-booleanfun/blob/3a75a656104e18dec6169c3f06f340ed9da43370/BooleanFun/Basic.lean#L594-L598

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

theorem BooleanFun.multiplier_walsh {m : ℕ → ℝ} {S : Finset (Fin n)} : multiplier m (χ S) = (m S.card)•χ S := by sorry
