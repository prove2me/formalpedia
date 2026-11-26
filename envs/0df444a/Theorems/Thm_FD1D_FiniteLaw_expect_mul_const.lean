-- Prove2me | Theorems.Thm_FD1D_FiniteLaw_expect_mul_const
-- name    : FD1D.FiniteLaw.expect_mul_const
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:42:14.702251+00:00
-- url     : https://prove2.me/theorems/a82d483a-cc1b-44c5-9614-1efe089d4e57
-- title:
--   Finite Law: expect mul const
-- statement:
--   The Finite Law construction uses the expect mul const property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Expectations.lean#L28-L33
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Expectations.lean#L28-L33

import Definitions.Def_FD1D_Markov
import Definitions.Def_FD1D_Expectations
set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators
open FD1D.FiniteLaw
variable {α : Type*} [Fintype α]

theorem FD1D.FiniteLaw.expect_mul_const (μ : FiniteLaw α) (f : α → ℝ) (c : ℝ) :
    μ.expect (fun x => f x * c) = μ.expect f * c := by sorry
