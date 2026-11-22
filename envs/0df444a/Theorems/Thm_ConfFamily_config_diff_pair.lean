-- Prove2me | Theorems.Thm_ConfFamily_config_diff_pair
-- name    : ConfFamily.config_diff_pair
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T20:41:36.082701+00:00
-- url     : https://prove2.me/theorems/dfcc3768-901c-4b77-b58c-84b6a7b0adbd
-- title:
--   Conf Family: config diff pair
-- statement:
--   The closing state of two backward steps.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Stable/LTSI.lean#L62-L72
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Stable/LTSI.lean#L62-L72

import Definitions.Def_EventStructures_Stable_Basic
import Definitions.Def_EventStructures_Family_LTSI
import Definitions.Def_EventStructures_Stable_LTSI
set_option autoImplicit true
open ConfFamily
variable {L : Type*} (F : ConfFamily L)
open ConfFamily
variable {F}

theorem ConfFamily.config_diff_pair (hF : Stable F) {c : Set F.Event} {e₁ e₂ : F.Event}
    (h₁ : F.Config (c \ {e₁})) (h₂ : F.Config (c \ {e₂})) (hc : F.Config c) :
    F.Config ((c \ {e₁}) ∩ (c \ {e₂})) := by sorry
