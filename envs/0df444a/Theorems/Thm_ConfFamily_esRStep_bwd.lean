-- Prove2me | Theorems.Thm_ConfFamily_esRStep_bwd
-- name    : ConfFamily.esRStep_bwd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:41:35.837234+00:00
-- url     : https://prove2.me/theorems/1e1a2370-903d-436a-9205-3a0131de4924
-- title:
--   Conf Family: es RStep bwd
-- statement:
--   A backward step is a forward step read the other way.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Stable/LTSI.lean#L54-L59
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Stable/LTSI.lean#L54-L59

import Definitions.Def_EventStructures_Stable_Basic
import Definitions.Def_EventStructures_Family_LTSI
import Definitions.Def_EventStructures_Stable_LTSI
set_option autoImplicit true
open ConfFamily
variable {L : Type*} (F : ConfFamily L)
open ConfFamily
variable {F}

theorem ConfFamily.esRStep_bwd {c c' : Conf F} {a : L} {e : F.Event}
    (hc : F.Config c'.val) (he : e ∈ c.val) (hlbl : F.label e = a)
    (htgt : c'.val = c.val \ {e}) : esRStep F c (DirLabel.bwd a) c' := by sorry
