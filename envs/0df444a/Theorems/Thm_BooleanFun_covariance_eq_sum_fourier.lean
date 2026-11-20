-- Prove2me | Theorems.Thm_BooleanFun_covariance_eq_sum_fourier
-- name    : BooleanFun.covariance_eq_sum_fourier
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:05:05.867167+00:00
-- url     : https://prove2.me/theorems/ed2ab450-9759-4010-923b-e84013ab1c15
-- title:
--   Boolean Fun: covariance eq sum fourier
-- statement:
--   The Boolean Fun construction uses the covariance eq sum fourier property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-booleanfun/blob/3a75a656104e18dec6169c3f06f340ed9da43370/BooleanFun/Basic.lean#L483-L486
-- source:
--   https://github.com/roos-j/lean-booleanfun/blob/3a75a656104e18dec6169c3f06f340ed9da43370/BooleanFun/Basic.lean#L483-L486

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

theorem BooleanFun.covariance_eq_sum_fourier (f g : BooleanFunc n) : covariance f g = ∑ S ∈ {S : Finset (Fin n) | S.Nonempty}, 𝓕 f S * 𝓕 g S := by sorry
