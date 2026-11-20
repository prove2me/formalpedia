-- Prove2me | Theorems.Thm_BooleanFun_eq_sum_fourier_of_fourier_weight
-- name    : BooleanFun.eq_sum_fourier_of_fourier_weight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:05:34.881554+00:00
-- url     : https://prove2.me/theorems/83400bde-ba0b-4029-b848-dc9328cef44f
-- title:
--   Boolean Fun: eq sum fourier of fourier weight
-- statement:
--   The Boolean Fun construction uses the eq sum fourier of fourier weight property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-booleanfun/blob/3a75a656104e18dec6169c3f06f340ed9da43370/BooleanFun/Basic.lean#L546-L559
-- source:
--   https://github.com/roos-j/lean-booleanfun/blob/3a75a656104e18dec6169c3f06f340ed9da43370/BooleanFun/Basic.lean#L546-L559

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

theorem BooleanFun.eq_sum_fourier_of_fourier_weight {k : ℕ} {f : BooleanFunc n} (h : fourierWeight k f = ‖f‖ ^ 2):
    f = ∑ S ∈ {S|S.card = k}, 𝓕 f S • χ S := by sorry
