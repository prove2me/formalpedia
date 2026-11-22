-- Prove2me | Theorems.Thm_CCS_Label_strip_map
-- name    : CCS.Label.strip_map
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:36:23.437798+00:00
-- url     : https://prove2.me/theorems/7d431495-10ca-4409-ab9d-071b5001f022
-- title:
--   Label: strip map
-- statement:
--   The Label construction uses the strip map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/CCS/Syntax.lean#L36-L36
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/CCS/Syntax.lean#L36-L36

import Mathlib.Tactic.Lemma
import Mathlib.Tactic.TypeStar
import Definitions.Def_EventStructures_CCS_Syntax
set_option autoImplicit true
open CCS
open CCS.Label
variable {Name Name' : Type*}

theorem CCS.Label.strip_map (a : Label Name) : (a.map some).strip = some a := by sorry
