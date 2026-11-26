-- Prove2me | Theorems.Thm_FD1D_FiniteLaw_expect_mono
-- name    : FD1D.FiniteLaw.expect_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:32:19.563828+00:00
-- url     : https://prove2.me/theorems/6d5cf90c-953a-4f37-a83f-ecd0d2ec636b
-- title:
--   Finite Law: expect mono
-- statement:
--   The Finite Law construction uses the expect mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Basic.lean#L39-L43
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Basic.lean#L39-L43

import Mathlib
import Definitions.Def_FD1D_Basic
set_option autoImplicit true
open FD1D
noncomputable section
open FD1D.FiniteLaw
variable {α β : Type*} [Fintype α] [Fintype β]

theorem FD1D.FiniteLaw.expect_mono (μ : FiniteLaw α) {f g : α → ℝ}
    (hfg : ∀ x, f x ≤ g x) : μ.expect f ≤ μ.expect g := by sorry
