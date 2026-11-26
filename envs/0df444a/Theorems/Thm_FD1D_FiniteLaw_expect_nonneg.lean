-- Prove2me | Theorems.Thm_FD1D_FiniteLaw_expect_nonneg
-- name    : FD1D.FiniteLaw.expect_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:32:12.122211+00:00
-- url     : https://prove2.me/theorems/02cf816f-59ce-55be-95b3-66954f7d4bd0
-- title:
--   Finite Law: expect nonneg
-- statement:
--   The Finite Law construction uses the expect nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Basic.lean#L35-L37
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Basic.lean#L35-L37

import Mathlib
import Definitions.Def_FD1D_Basic
set_option autoImplicit true
open FD1D
noncomputable section
open FD1D.FiniteLaw
variable {α β : Type*} [Fintype α] [Fintype β]

theorem FD1D.FiniteLaw.expect_nonneg (μ : FiniteLaw α) {f : α → ℝ}
    (hf : ∀ x, 0 ≤ f x) : 0 ≤ μ.expect f := by sorry
