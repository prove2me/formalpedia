-- Prove2me | Theorems.Thm_CCS_projR_eq_pmap
-- name    : CCS.projR_eq_pmap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T21:10:36.348801+00:00
-- url     : https://prove2.me/theorems/fba45756-4d69-4d41-b852-67427d23f011
-- title:
--   CCS: proj R eq pmap
-- statement:
--   The CCS construction uses the proj R eq pmap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/CCS/Par.lean#L277-L278
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/CCS/Par.lean#L277-L278

import Definitions.Def_EventStructures_General_Stable
import Definitions.Def_EventStructures_Stable_Basic
import Definitions.Def_EventStructures_CCS_Syntax
import Definitions.Def_EventStructures_CCS_Par
set_option autoImplicit true
open GES
open CCS
variable {Name : Type*}
variable {E F : SES (Action Name)}
variable {c : Set (Tag E F)}

theorem CCS.projR_eq_pmap (c : Set (Tag E F)) :
    projR c = GES.pmapSet (G := (parSES E F).toGES) (H := F.toGES) Tag.evR c := by sorry
