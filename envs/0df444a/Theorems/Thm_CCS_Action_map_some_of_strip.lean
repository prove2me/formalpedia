-- Prove2me | Theorems.Thm_CCS_Action_map_some_of_strip
-- name    : CCS.Action.map_some_of_strip
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T20:46:18.510785+00:00
-- url     : https://prove2.me/theorems/8c1bc6ad-d8b2-419b-901c-e0ee80930e76
-- title:
--   Action: map some of strip
-- statement:
--   `strip` inverts `map some`.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/CCS/Syntax.lean#L63-L77
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/CCS/Syntax.lean#L63-L77

import Mathlib.Tactic.Lemma
import Mathlib.Tactic.TypeStar
import Definitions.Def_EventStructures_CCS_Syntax
set_option autoImplicit true
open CCS
open CCS.Action
variable {Name Name' : Type*}

theorem CCS.Action.map_some_of_strip : ∀ {b : Action (Option Name)} {a : Action Name},
    b.strip = some a → b = Action.map some a
  := by sorry
