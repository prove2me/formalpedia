-- Prove2me | Theorems.Thm_FD1D_FiniteLaw_timeLiftPerm_apply
-- name    : FD1D.FiniteLaw.timeLiftPerm_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:43:51.848088+00:00
-- url     : https://prove2.me/theorems/d9f48995-bcbc-4acf-a5a4-a47a855647e0
-- title:
--   Finite Law: time Lift Perm apply
-- statement:
--   The Finite Law construction uses the time Lift Perm apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Averaging.lean#L88-L91
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Averaging.lean#L88-L91

import Definitions.Def_FD1D_Expectations
import Definitions.Def_FD1D_Averaging
set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators
open FD1D.FiniteLaw
variable {α : Type*} [Fintype α]

theorem FD1D.FiniteLaw.timeLiftPerm_apply {T : ℕ} (e : Equiv.Perm α)
    (t : Fin T) (x : α) :
    timeLiftPerm e (t, x) = (t, e x) := by sorry

attribute [defeq] FD1D.FiniteLaw.timeLiftPerm_apply
