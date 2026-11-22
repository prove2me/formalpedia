-- Prove2me | Theorems.Thm_ConfFamily_TraceEquivFrom_append_left
-- name    : ConfFamily.TraceEquivFrom.append_left
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:43:51.273722+00:00
-- url     : https://prove2.me/theorems/44ec0d57-8336-4073-95f8-42686eddcdd7
-- title:
--   Trace Equiv From: append left
-- statement:
--   The Trace Equiv From construction uses the append left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Family/Trace.lean#L180-L189
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Family/Trace.lean#L180-L189

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

theorem ConfFamily.TraceEquivFrom.append_left {c : Set F.Event} {t₁ t₂ : List F.Event}
    (h : TraceEquivFrom F c t₁ t₂) (t : List F.Event) :
    TraceEquivFrom F c (t₁ ++ t) (t₂ ++ t) := by sorry
