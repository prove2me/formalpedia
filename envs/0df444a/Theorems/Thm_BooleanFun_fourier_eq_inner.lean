-- Prove2me | Theorems.Thm_BooleanFun_fourier_eq_inner
-- name    : BooleanFun.fourier_eq_inner
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:03:50.954803+00:00
-- url     : https://prove2.me/theorems/5e85482f-2156-4ac3-9547-e4a53ea21a98
-- title:
--   Boolean Fun: fourier eq inner
-- statement:
--   The Boolean Fun construction uses the fourier eq inner property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-booleanfun/blob/3a75a656104e18dec6169c3f06f340ed9da43370/BooleanFun/Basic.lean#L248-L248
-- source:
--   https://github.com/roos-j/lean-booleanfun/blob/3a75a656104e18dec6169c3f06f340ed9da43370/BooleanFun/Basic.lean#L248-L248

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

theorem BooleanFun.fourier_eq_inner : 𝓕 f S = ⟪χ S, f⟫ := by sorry
