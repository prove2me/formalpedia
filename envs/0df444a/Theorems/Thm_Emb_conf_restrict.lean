-- Prove2me | Theorems.Thm_Emb_conf_restrict
-- name    : Emb.conf_restrict
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:40:53.313031+00:00
-- url     : https://prove2.me/theorems/2d65d2a4-2632-4d5b-9ffb-72f84b96e0fa
-- title:
--   Emb: conf restrict
-- statement:
--   The Emb construction uses the conf restrict property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Prime/Configuration.lean#L84-L86
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Prime/Configuration.lean#L84-L86

import Definitions.Def_EventStructures_Prime_Basic
import Definitions.Def_EventStructures_Family_Basic
import Mathlib.Order.Preorder.Finite
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Finite.Basic
import Definitions.Def_EventStructures_Prime_Configuration
set_option autoImplicit true
variable {L : Type*} (es : PES L)
open Emb
variable {L : Type*} {E F : PES L} (ι : Emb E F)

theorem Emb.conf_restrict {c : Set F.Event} (h : _root_.isConf F c) :
    _root_.isConf E {y | ι.f y ∈ c} := by sorry
