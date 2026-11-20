-- Prove2me | Theorems.Thm_BooleanFun_eq_sum_degree_one_of_fourier_weight_one
-- name    : BooleanFun.eq_sum_degree_one_of_fourier_weight_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:04:27.419485+00:00
-- url     : https://prove2.me/theorems/2a11ff0e-f5f9-4cc9-bf20-846e140c2cd2
-- title:
--   Boolean Fun: eq sum degree one of fourier weight one
-- statement:
--   The Boolean Fun construction uses the eq sum degree one of fourier weight one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-booleanfun/blob/3a75a656104e18dec6169c3f06f340ed9da43370/BooleanFun/Basic.lean#L561-L567
-- source:
--   https://github.com/roos-j/lean-booleanfun/blob/3a75a656104e18dec6169c3f06f340ed9da43370/BooleanFun/Basic.lean#L561-L567

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

theorem BooleanFun.eq_sum_degree_one_of_fourier_weight_one {f : BooleanFunc n} (h : fourierWeight 1 f = ‖f‖ ^ 2) :
    ∀ x, f x = ∑ i, 𝓕 f {i} * (-1)^(x i).val := by sorry
