-- Prove2me | Theorems.Thm_Configuration_enables_extension
-- name    : Configuration.enables_extension
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:40:35.262843+00:00
-- url     : https://prove2.me/theorems/b35e99d3-d46f-4c74-873a-cfabe3048b6b
-- title:
--   Configuration: enables extension
-- statement:
--   If a configuration c enables an event e, then c ∪ {e} is also a configuration.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Prime/Configuration.lean#L32-L61
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Prime/Configuration.lean#L32-L61

import Definitions.Def_EventStructures_Prime_Basic
import Definitions.Def_EventStructures_Family_Basic
import Mathlib.Order.Preorder.Finite
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Finite.Basic
import Definitions.Def_EventStructures_Prime_Configuration
import Theorems.Thm_ConfFamily_enables_extension

set_option autoImplicit true
variable {L : Type*} (es : PES L)
open Configuration
local infix:50 " ⊢ " => enables es

theorem Configuration.enables_extension {c : Set es.Event} {e : es.Event} (h : c ⊢ e) :
    isConf es (c ∪ {e}) := by sorry
