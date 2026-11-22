-- Prove2me | Theorems.Thm_ConfFamily_Indep_irrefl
-- name    : ConfFamily.Indep.irrefl
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:46:27.573045+00:00
-- url     : https://prove2.me/theorems/1ea7f877-a825-4559-a186-656ad1b11789
-- title:
--   Indep: irrefl
-- statement:
--   Independence is irreflexive.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Family/Basic.lean#L70-L71
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Family/Basic.lean#L70-L71

import Mathlib.Tactic.Lemma
import Mathlib.Tactic.TypeStar
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Order.Basic
import Definitions.Def_EventStructures_Family_Basic
set_option autoImplicit true
open ConfFamily
variable {L : Type*} (F : ConfFamily L)
variable {F}
variable (F)
variable {F}

theorem ConfFamily.Indep.irrefl {c : Set F.Event} {e : F.Event} : ¬ F.Indep c e e := by sorry
