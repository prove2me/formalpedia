-- Prove2me | Theorems.Thm_FD1D_FiniteKernel_IsStationary_expect_eq
-- name    : FD1D.FiniteKernel.IsStationary.expect_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:42:56.71402+00:00
-- url     : https://prove2.me/theorems/b92a6c73-7bfa-4c82-bde0-bf4757ea8b75
-- title:
--   Is Stationary: expect eq
-- statement:
--   The Is Stationary construction uses the expect eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Expectations.lean#L75-L78
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Expectations.lean#L75-L78

import Definitions.Def_FD1D_Markov
import Definitions.Def_FD1D_Expectations
set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators
open FD1D.FiniteKernel
variable {α : Type*} [Fintype α]

theorem FD1D.FiniteKernel.IsStationary.expect_eq {K : FiniteKernel α} {μ : FiniteLaw α}
    (hμ : K.IsStationary μ) (f : α → ℝ) :
    (K.step μ).expect f = μ.expect f := by sorry
