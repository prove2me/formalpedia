-- Prove2me | Theorems.Thm_BooleanFun_inner_eq_expectation
-- name    : BooleanFun.inner_eq_expectation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:03:04.561193+00:00
-- url     : https://prove2.me/theorems/4f9b0043-8649-4824-838d-a97438c6f1ce
-- title:
--   Boolean Fun: inner eq expectation
-- statement:
--   The Boolean Fun construction uses the inner eq expectation property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-booleanfun/blob/3a75a656104e18dec6169c3f06f340ed9da43370/BooleanFun/Basic.lean#L246-L246
-- source:
--   https://github.com/roos-j/lean-booleanfun/blob/3a75a656104e18dec6169c3f06f340ed9da43370/BooleanFun/Basic.lean#L246-L246

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

theorem BooleanFun.inner_eq_expectation : ⟪f, g⟫ = 𝐄 (f * g) := by sorry
