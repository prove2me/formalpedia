-- Prove2me | Theorems.Thm_DirLabel_rev_rev
-- name    : DirLabel.rev_rev
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T20:48:44.968403+00:00
-- url     : https://prove2.me/theorems/e754ddc0-eed3-41be-a4c2-b7443485f337
-- title:
--   Dir Label: rev rev
-- statement:
--   Reversal is an involution.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/LTS/Basic.lean#L76-L76
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/LTS/Basic.lean#L76-L76

import Mathlib.Tactic.Lemma
import Mathlib.Tactic.TypeStar
import Definitions.Def_EventStructures_LTS_Basic
set_option autoImplicit true
variable {L : Type*}
open DirLabel

theorem DirLabel.rev_rev (la : DirLabel L) : rev (rev la) = la := by sorry
