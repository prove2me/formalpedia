-- Prove2me | Theorems.Thm_ConfFamily_enables_of
-- name    : ConfFamily.enables_of
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T20:46:28.894489+00:00
-- url     : https://prove2.me/theorems/c9da0cba-09f7-4ddf-af63-76a8dcd95a4f
-- title:
--   Conf Family: enables of
-- statement:
--   The Conf Family construction uses the enables of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Family/Basic.lean#L46-L47
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Family/Basic.lean#L46-L47

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

theorem ConfFamily.enables_of {c : Set F.Event} {e : F.Event} (hc : F.Config c)
    (hx : F.Config (c ∪ {e})) : F.enables c e := by sorry
