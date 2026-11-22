-- Prove2me | Theorems.Thm_Emb_finite
-- name    : Emb.finite
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:47:28.271405+00:00
-- url     : https://prove2.me/theorems/c9f2ed39-e16e-4c84-80de-ede31b9cafd3
-- title:
--   Emb: finite
-- statement:
--   The Emb construction uses the finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Prime/Configuration.lean#L81-L82
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Prime/Configuration.lean#L81-L82

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

theorem Emb.finite {c : Set F.Event} (h : c.Finite) : {y | ι.f y ∈ c}.Finite := by sorry
