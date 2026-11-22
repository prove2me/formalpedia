-- Prove2me | Theorems.Thm_ConfFamily_TraceEquivFrom_trans
-- name    : ConfFamily.TraceEquivFrom.trans
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:42:39.597792+00:00
-- url     : https://prove2.me/theorems/8d3fd1aa-7121-47e2-ae18-381283dddc6e
-- title:
--   Trace Equiv From: trans
-- statement:
--   The Trace Equiv From construction uses the trans property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Family/Trace.lean#L157-L162
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Family/Trace.lean#L157-L162

import Mathlib.Tactic.Lemma
import Mathlib.Tactic.TypeStar
import Mathlib.Algebra.Group.Defs
import Mathlib.Order.Basic
import Definitions.Def_EventStructures_Family_Basic
import Definitions.Def_EventStructures_Family_Trace
set_option autoImplicit true
variable {α L : Type*} (R : α → α → Prop) (lbl : α → L)
local infixr:60 " ≈ₜ " => TraceEquiv R
open ConfFamily
variable {L : Type*} {F : ConfFamily L}
open ConfFamily.TraceEquivFrom

theorem ConfFamily.TraceEquivFrom.trans {c : Set F.Event} {t₁ t₂ t₃ : List F.Event}
    (h₁₂ : TraceEquivFrom F c t₁ t₂) (h₂₃ : TraceEquivFrom F c t₂ t₃) :
    TraceEquivFrom F c t₁ t₃ := by sorry
