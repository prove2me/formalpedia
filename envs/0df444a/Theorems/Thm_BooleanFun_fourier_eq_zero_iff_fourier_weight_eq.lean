-- Prove2me | Theorems.Thm_BooleanFun_fourier_eq_zero_iff_fourier_weight_eq
-- name    : BooleanFun.fourier_eq_zero_iff_fourier_weight_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:03:01.208483+00:00
-- url     : https://prove2.me/theorems/19dd1645-1eeb-4c77-9d52-5f1f35118dbd
-- title:
--   Boolean Fun: fourier eq zero iff fourier weight eq
-- statement:
--   The Boolean Fun construction uses the fourier eq zero iff fourier weight eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-booleanfun/blob/3a75a656104e18dec6169c3f06f340ed9da43370/BooleanFun/Basic.lean#L518-L544
-- source:
--   https://github.com/roos-j/lean-booleanfun/blob/3a75a656104e18dec6169c3f06f340ed9da43370/BooleanFun/Basic.lean#L518-L544

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

theorem BooleanFun.fourier_eq_zero_iff_fourier_weight_eq {k : ℕ} {f : BooleanFunc n}:
    (∀ S, S.card ≠ k → 𝓕 f S = 0) ↔ fourierWeight k f = ‖f‖ ^ 2 := by sorry
