-- Prove2me | Theorems.Thm_CCS_Label_co_co
-- name    : CCS.Label.co_co
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:36:21.796427+00:00
-- url     : https://prove2.me/theorems/6230759c-cac2-42bb-92de-3cacaaf5fbd2
-- title:
--   Label: co co
-- statement:
--   The Label construction uses the co co property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/CCS/Syntax.lean#L22-L22
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/CCS/Syntax.lean#L22-L22

import Mathlib.Tactic.Lemma
import Mathlib.Tactic.TypeStar
import Definitions.Def_EventStructures_CCS_Syntax
set_option autoImplicit true
open CCS
open CCS.Label
variable {Name Name' : Type*}

theorem CCS.Label.co_co (a : Label Name) : a.co.co = a := by sorry
