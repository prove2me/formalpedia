-- Prove2me | Theorems.Thm_Bisimilar_symm
-- name    : Bisimilar.symm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:36:24.740225+00:00
-- url     : https://prove2.me/theorems/6d343513-1d5c-4a9b-a28f-25b95c408f5c
-- title:
--   Bisimilar: symm
-- statement:
--   The Bisimilar construction uses the symm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/LTS/Basic.lean#L49-L51
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/LTS/Basic.lean#L49-L51

import Mathlib.Tactic.Lemma
import Mathlib.Tactic.TypeStar
import Definitions.Def_EventStructures_LTS_Basic
set_option autoImplicit true
variable {L : Type*}

theorem Bisimilar.symm {S T : LTSI L} : Bisimilar S T → Bisimilar T S := by sorry
