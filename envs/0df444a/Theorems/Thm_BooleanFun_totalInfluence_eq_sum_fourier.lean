-- Prove2me | Theorems.Thm_BooleanFun_totalInfluence_eq_sum_fourier
-- name    : BooleanFun.totalInfluence_eq_sum_fourier
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:05:00.570881+00:00
-- url     : https://prove2.me/theorems/912f22f6-17cf-4149-a0b3-6aa4422d87aa
-- title:
--   Boolean Fun: total Influence eq sum fourier
-- statement:
--   The Boolean Fun construction uses the total Influence eq sum fourier property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-booleanfun/blob/3a75a656104e18dec6169c3f06f340ed9da43370/BooleanFun/Basic.lean#L469-L475
-- source:
--   https://github.com/roos-j/lean-booleanfun/blob/3a75a656104e18dec6169c3f06f340ed9da43370/BooleanFun/Basic.lean#L469-L475

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

theorem BooleanFun.totalInfluence_eq_sum_fourier (f : BooleanFunc n) : totalInfluence f = ∑ S, S.card * (𝓕 f S) ^ 2 := by sorry
