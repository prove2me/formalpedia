-- Prove2me | Theorems.Thm_CCS_Action_strip_map
-- name    : CCS.Action.strip_map
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:36:22.273984+00:00
-- url     : https://prove2.me/theorems/be9ba8a4-d988-4f83-8a33-efd095c1b666
-- title:
--   Action: strip map
-- statement:
--   The Action construction uses the strip map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/CCS/Syntax.lean#L59-L60
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/CCS/Syntax.lean#L59-L60

import Mathlib.Tactic.Lemma
import Mathlib.Tactic.TypeStar
import Definitions.Def_EventStructures_CCS_Syntax
set_option autoImplicit true
open CCS
open CCS.Action
variable {Name Name' : Type*}

theorem CCS.Action.strip_map (α : Action Name) : (α.map some).strip = some α := by sorry
