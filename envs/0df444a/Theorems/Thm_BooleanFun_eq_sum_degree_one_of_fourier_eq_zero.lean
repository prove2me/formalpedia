-- Prove2me | Theorems.Thm_BooleanFun_eq_sum_degree_one_of_fourier_eq_zero
-- name    : BooleanFun.eq_sum_degree_one_of_fourier_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:10:03.924752+00:00
-- url     : https://prove2.me/theorems/a4dcd203-8ed5-49ff-957a-bfc6b0afb84a
-- title:
--   Boolean Fun: eq sum degree one of fourier eq zero
-- statement:
--   The Boolean Fun construction uses the eq sum degree one of fourier eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-booleanfun/blob/3a75a656104e18dec6169c3f06f340ed9da43370/BooleanFun/Basic.lean#L569-L571
-- source:
--   https://github.com/roos-j/lean-booleanfun/blob/3a75a656104e18dec6169c3f06f340ed9da43370/BooleanFun/Basic.lean#L569-L571

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

theorem BooleanFun.eq_sum_degree_one_of_fourier_eq_zero {f : BooleanFunc n} (h : ∀ S, S.card ≠ 1 → 𝓕 f S = 0):
    ∀ x, f x = ∑ i, 𝓕 f {i} * (-1)^(x i).val := by sorry
