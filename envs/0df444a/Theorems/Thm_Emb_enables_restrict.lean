-- Prove2me | Theorems.Thm_Emb_enables_restrict
-- name    : Emb.enables_restrict
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T20:47:37.368803+00:00
-- url     : https://prove2.me/theorems/ef60c8c6-536a-4d39-8884-44ab9045555a
-- title:
--   Emb: enables restrict
-- statement:
--   The Emb construction uses the enables restrict property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Prime/Configuration.lean#L88-L91
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Prime/Configuration.lean#L88-L91

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

theorem Emb.enables_restrict {c : Set F.Event} {x : E.Event} (hc : _root_.isConf F c)
    (h : Configuration.enables F c (ι.f x)) :
    Configuration.enables E {y | ι.f y ∈ c} x := by sorry
