-- Prove2me | Theorems.Thm_ConfFamily_inter_diff_union
-- name    : ConfFamily.inter_diff_union
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:40:22.950702+00:00
-- url     : https://prove2.me/theorems/80529c46-07f8-4346-a005-754bdb4c63e7
-- title:
--   Conf Family: inter diff union
-- statement:
--   Re-adding one of the two removed events.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Stable/LTSI.lean#L75-L86
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Stable/LTSI.lean#L75-L86

import Definitions.Def_EventStructures_Stable_Basic
import Definitions.Def_EventStructures_Family_LTSI
import Definitions.Def_EventStructures_Stable_LTSI
set_option autoImplicit true
open ConfFamily
variable {L : Type*} (F : ConfFamily L)
open ConfFamily
variable {F}

theorem ConfFamily.inter_diff_union {c : Set F.Event} {e₁ e₂ : F.Event}
    (he₂ : e₂ ∈ c) (hne : e₁ ≠ e₂) :
    ((c \ {e₁}) ∩ (c \ {e₂})) ∪ {e₂} = c \ {e₁} := by sorry
