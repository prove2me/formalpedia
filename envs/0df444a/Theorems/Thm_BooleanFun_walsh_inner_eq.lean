-- Prove2me | Theorems.Thm_BooleanFun_walsh_inner_eq
-- name    : BooleanFun.walsh_inner_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:02:59.809174+00:00
-- url     : https://prove2.me/theorems/12fbebc1-d332-4f2e-b0f7-4c56d911f5cc
-- title:
--   Boolean Fun: walsh inner eq
-- statement:
--   The Boolean Fun construction uses the walsh inner eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-booleanfun/blob/3a75a656104e18dec6169c3f06f340ed9da43370/BooleanFun/Basic.lean#L307-L311
-- source:
--   https://github.com/roos-j/lean-booleanfun/blob/3a75a656104e18dec6169c3f06f340ed9da43370/BooleanFun/Basic.lean#L307-L311

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

theorem BooleanFun.walsh_inner_eq : ⟪χ S, χ S'⟫ = oneOn (S = S') := by sorry
