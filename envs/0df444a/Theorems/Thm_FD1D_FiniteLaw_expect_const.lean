-- Prove2me | Theorems.Thm_FD1D_FiniteLaw_expect_const
-- name    : FD1D.FiniteLaw.expect_const
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:32:14.555347+00:00
-- url     : https://prove2.me/theorems/cd981cfc-6978-597b-abad-a2b593463deb
-- title:
--   Finite Law: expect const
-- statement:
--   The Finite Law construction uses the expect const property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Basic.lean#L31-L33
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Basic.lean#L31-L33

import Mathlib
import Definitions.Def_FD1D_Basic
set_option autoImplicit true
open FD1D
noncomputable section
open FD1D.FiniteLaw
variable {α β : Type*} [Fintype α] [Fintype β]

theorem FD1D.FiniteLaw.expect_const (μ : FiniteLaw α) (c : ℝ) :
    μ.expect (fun _ => c) = c := by sorry
