-- Prove2me | Theorems.Thm_ConfFamily_TraceEquivFrom_reach_eq
-- name    : ConfFamily.TraceEquivFrom.reach_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:48:34.664363+00:00
-- url     : https://prove2.me/theorems/516cd8ae-abfc-4512-9086-bf2ef26f5299
-- title:
--   Trace Equiv From: reach eq
-- statement:
--   Equivalent traces use the same events, so reach the same configuration.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Family/Trace.lean#L172-L178
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Family/Trace.lean#L172-L178

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

theorem ConfFamily.TraceEquivFrom.reach_eq {c : Set F.Event} {t₁ t₂ : List F.Event} (h : TraceEquivFrom F c t₁ t₂) :
    reach F c t₁ = reach F c t₂ := by sorry
