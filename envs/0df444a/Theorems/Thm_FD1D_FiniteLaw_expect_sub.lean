-- Prove2me | Theorems.Thm_FD1D_FiniteLaw_expect_sub
-- name    : FD1D.FiniteLaw.expect_sub
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:41:03.417741+00:00
-- url     : https://prove2.me/theorems/277f4041-eac0-4b50-9304-794dc2cde059
-- title:
--   Finite Law: expect sub
-- statement:
--   The Finite Law construction uses the expect sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Expectations.lean#L17-L19
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Expectations.lean#L17-L19

import Definitions.Def_FD1D_Markov
import Definitions.Def_FD1D_Expectations
set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators
open FD1D.FiniteLaw
variable {α : Type*} [Fintype α]

theorem FD1D.FiniteLaw.expect_sub (μ : FiniteLaw α) (f g : α → ℝ) :
    μ.expect (fun x => f x - g x) = μ.expect f - μ.expect g := by sorry
