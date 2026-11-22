-- Prove2me | Theorems.Thm_ConfFamily_enables_extension
-- name    : ConfFamily.enables_extension
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:36:28.144435+00:00
-- url     : https://prove2.me/theorems/895465ca-7d28-4844-9813-0869d9a766ae
-- title:
--   Conf Family: enables extension
-- statement:
--   The Conf Family construction uses the enables extension property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Family/Basic.lean#L43-L44
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Family/Basic.lean#L43-L44

import Mathlib.Tactic.Lemma
import Mathlib.Tactic.TypeStar
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Order.Basic
import Definitions.Def_EventStructures_Family_Basic
set_option autoImplicit true
open ConfFamily
variable {L : Type*} (F : ConfFamily L)
variable {F}

theorem ConfFamily.enables_extension {c : Set F.Event} {e : F.Event} (h : F.enables c e) :
    F.Config (c ∪ {e}) := by sorry
