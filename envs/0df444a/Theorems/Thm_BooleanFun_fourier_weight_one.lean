-- Prove2me | Theorems.Thm_BooleanFun_fourier_weight_one
-- name    : BooleanFun.fourier_weight_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:09:34.901224+00:00
-- url     : https://prove2.me/theorems/aab89045-f401-4b63-adcd-43365a71a295
-- title:
--   Boolean Fun: fourier weight one
-- statement:
--   The Boolean Fun construction uses the fourier weight one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-booleanfun/blob/3a75a656104e18dec6169c3f06f340ed9da43370/BooleanFun/Basic.lean#L515-L516
-- source:
--   https://github.com/roos-j/lean-booleanfun/blob/3a75a656104e18dec6169c3f06f340ed9da43370/BooleanFun/Basic.lean#L515-L516

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

theorem BooleanFun.fourier_weight_one {f : BooleanFunc n} : fourierWeight 1 f = fourierWeightOne f := by sorry
