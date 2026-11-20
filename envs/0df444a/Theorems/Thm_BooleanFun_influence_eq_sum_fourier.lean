-- Prove2me | Theorems.Thm_BooleanFun_influence_eq_sum_fourier
-- name    : BooleanFun.influence_eq_sum_fourier
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:04:50.406645+00:00
-- url     : https://prove2.me/theorems/b82eade8-b410-4c3e-abbc-20006b83d1d9
-- title:
--   Boolean Fun: influence eq sum fourier
-- statement:
--   The Boolean Fun construction uses the influence eq sum fourier property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-booleanfun/blob/3a75a656104e18dec6169c3f06f340ed9da43370/BooleanFun/Basic.lean#L447-L464
-- source:
--   https://github.com/roos-j/lean-booleanfun/blob/3a75a656104e18dec6169c3f06f340ed9da43370/BooleanFun/Basic.lean#L447-L464

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

theorem BooleanFun.influence_eq_sum_fourier (f : BooleanFunc n) (i : Fin n):
    influence f i = ∑ S ∈ {S | i ∈ S}, (𝓕 f S) ^ 2 := by sorry
