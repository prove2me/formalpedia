-- Prove2me | Theorems.Thm_ConfFamily_union_diff_singleton
-- name    : ConfFamily.union_diff_singleton
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T20:41:27.962182+00:00
-- url     : https://prove2.me/theorems/37fc93d6-408c-428b-8892-5839c2e4e88c
-- title:
--   Conf Family: union diff singleton
-- statement:
--   Removing and re-adding a present event leaves a configuration unchanged.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Stable/LTSI.lean#L41-L51
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Stable/LTSI.lean#L41-L51

import Definitions.Def_EventStructures_Stable_Basic
import Definitions.Def_EventStructures_Family_LTSI
import Definitions.Def_EventStructures_Stable_LTSI
set_option autoImplicit true
open ConfFamily
variable {L : Type*} (F : ConfFamily L)
open ConfFamily
variable {F}

theorem ConfFamily.union_diff_singleton {c : Set F.Event} {e : F.Event} (he : e ∈ c) :
    (c \ {e}) ∪ {e} = c := by sorry
