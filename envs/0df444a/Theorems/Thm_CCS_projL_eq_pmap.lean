-- Prove2me | Theorems.Thm_CCS_projL_eq_pmap
-- name    : CCS.projL_eq_pmap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T21:10:34.018168+00:00
-- url     : https://prove2.me/theorems/03985d29-0f90-4ffd-8b0f-0b19a80a0889
-- title:
--   CCS: proj L eq pmap
-- statement:
--   The CCS construction uses the proj L eq pmap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/CCS/Par.lean#L274-L275
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/CCS/Par.lean#L274-L275

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

theorem CCS.projL_eq_pmap (c : Set (Tag E F)) :
    projL c = GES.pmapSet (G := (parSES E F).toGES) (H := E.toGES) Tag.evL c := by sorry
