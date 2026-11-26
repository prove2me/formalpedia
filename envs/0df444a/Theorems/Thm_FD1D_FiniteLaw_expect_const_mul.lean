-- Prove2me | Theorems.Thm_FD1D_FiniteLaw_expect_const_mul
-- name    : FD1D.FiniteLaw.expect_const_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:42:07.83241+00:00
-- url     : https://prove2.me/theorems/5788f9bc-992d-476d-a44b-dde9d61101a8
-- title:
--   Finite Law: expect const mul
-- statement:
--   The Finite Law construction uses the expect const mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Expectations.lean#L21-L26
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Expectations.lean#L21-L26

import Definitions.Def_FD1D_Markov
import Definitions.Def_FD1D_Expectations
set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators
open FD1D.FiniteLaw
variable {α : Type*} [Fintype α]

theorem FD1D.FiniteLaw.expect_const_mul (μ : FiniteLaw α) (c : ℝ) (f : α → ℝ) :
    μ.expect (fun x => c * f x) = c * μ.expect f := by sorry
