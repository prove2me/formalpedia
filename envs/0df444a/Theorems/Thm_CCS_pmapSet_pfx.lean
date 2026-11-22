-- Prove2me | Theorems.Thm_CCS_pmapSet_pfx
-- name    : CCS.pmapSet_pfx
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:54:39.76385+00:00
-- url     : https://prove2.me/theorems/46b72be1-98cb-4089-a9ed-6be2c3a242fa
-- title:
--   CCS: pmap Set pfx
-- statement:
--   The CCS construction uses the pmap Set pfx property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/CCS/Semantics.lean#L214-L218
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/CCS/Semantics.lean#L214-L218

import Definitions.Def_EventStructures_Prime_Basic
import Definitions.Def_EventStructures_LTS_Basic
import Definitions.Def_EventStructures_Prime_LTSI
import Definitions.Def_EventStructures_CCS_Syntax
import Definitions.Def_EventStructures_CCS_Par
import Definitions.Def_EventStructures_CCS_Semantics
set_option autoImplicit true
open PES Configuration ConfFamily
open CCS
variable {Name : Type*}
variable {Name : Type*}
variable {E F : SES (Action Name)} {α : Action Name}

theorem CCS.pmapSet_pfx (s : Set (Option E.Event)) :
    GES.pmapSet (G := (pfx α E).toGES) (H := E.toGES) id s = {z | some z ∈ s} := by sorry
