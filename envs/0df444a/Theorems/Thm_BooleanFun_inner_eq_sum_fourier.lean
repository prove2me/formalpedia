-- Prove2me | Theorems.Thm_BooleanFun_inner_eq_sum_fourier
-- name    : BooleanFun.inner_eq_sum_fourier
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:03:05.167198+00:00
-- url     : https://prove2.me/theorems/2e253aa5-84f5-4c04-8872-7865d46ac9b5
-- title:
--   Boolean Fun: inner eq sum fourier
-- statement:
--   Plancherel/Parseval theorem for Boolean functions.
--
--   Source: https://github.com/roos-j/lean-booleanfun/blob/3a75a656104e18dec6169c3f06f340ed9da43370/BooleanFun/Basic.lean#L338-L344
-- source:
--   https://github.com/roos-j/lean-booleanfun/blob/3a75a656104e18dec6169c3f06f340ed9da43370/BooleanFun/Basic.lean#L338-L344

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

theorem BooleanFun.inner_eq_sum_fourier : ⟪f, g⟫ = ∑ S : Finset (Fin n), (𝓕 f S) * (𝓕 g S) := by sorry
