-- Prove2me | Theorems.Thm_BooleanFun_variance_eq_sum_fourier
-- name    : BooleanFun.variance_eq_sum_fourier
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:05:10.69121+00:00
-- url     : https://prove2.me/theorems/21326c25-e7f5-4f03-b153-5bafc778228d
-- title:
--   Boolean Fun: variance eq sum fourier
-- statement:
--   The Boolean Fun construction uses the variance eq sum fourier property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-booleanfun/blob/3a75a656104e18dec6169c3f06f340ed9da43370/BooleanFun/Basic.lean#L488-L489
-- source:
--   https://github.com/roos-j/lean-booleanfun/blob/3a75a656104e18dec6169c3f06f340ed9da43370/BooleanFun/Basic.lean#L488-L489

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

theorem BooleanFun.variance_eq_sum_fourier (f : BooleanFunc n) : variance f = ∑ S ∈ {S : Finset (Fin n) | S.Nonempty}, (𝓕 f S) ^ 2 := by sorry
