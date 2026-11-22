-- Prove2me | Theorems.Thm_ConfFamily_TraceEquivFrom_symm
-- name    : ConfFamily.TraceEquivFrom.symm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:42:37.536657+00:00
-- url     : https://prove2.me/theorems/6b88f9ad-15b5-4b4d-92a1-e8c160d162a6
-- title:
--   Trace Equiv From: symm
-- statement:
--   The Trace Equiv From construction uses the symm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Family/Trace.lean#L164-L169
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Family/Trace.lean#L164-L169

import Mathlib.Tactic.Lemma
import Mathlib.Tactic.TypeStar
import Mathlib.Algebra.Group.Defs
import Mathlib.Order.Basic
import Definitions.Def_EventStructures_Family_Basic
import Definitions.Def_EventStructures_Family_Trace
import Theorems.Thm_ConfFamily_Indep_symm

set_option autoImplicit true
variable {α L : Type*} (R : α → α → Prop) (lbl : α → L)
local infixr:60 " ≈ₜ " => TraceEquiv R
open ConfFamily
variable {L : Type*} {F : ConfFamily L}
open ConfFamily.TraceEquivFrom

theorem ConfFamily.TraceEquivFrom.symm {c : Set F.Event} {t₁ t₂ : List F.Event} :
    TraceEquivFrom F c t₁ t₂ → TraceEquivFrom F c t₂ t₁ := by sorry
