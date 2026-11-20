-- Prove2me | Theorems.Thm_BooleanFun_laplace_eq_sum_fourier
-- name    : BooleanFun.laplace_eq_sum_fourier
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:04:47.647674+00:00
-- url     : https://prove2.me/theorems/5274f353-782e-421d-a856-fcd178e59583
-- title:
--   Boolean Fun: laplace eq sum fourier
-- statement:
--   The Boolean Fun construction uses the laplace eq sum fourier property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-booleanfun/blob/3a75a656104e18dec6169c3f06f340ed9da43370/BooleanFun/Basic.lean#L437-L442
-- source:
--   https://github.com/roos-j/lean-booleanfun/blob/3a75a656104e18dec6169c3f06f340ed9da43370/BooleanFun/Basic.lean#L437-L442

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

theorem BooleanFun.laplace_eq_sum_fourier (i : Fin n) (f : BooleanFunc n) : laplace i f = ∑ S ∈ {S | i ∈ S}, 𝓕 f S•χ (S) := by sorry
