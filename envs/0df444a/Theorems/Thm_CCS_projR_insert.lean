-- Prove2me | Theorems.Thm_CCS_projR_insert
-- name    : CCS.projR_insert
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:53:10.501736+00:00
-- url     : https://prove2.me/theorems/b6a1e13a-2834-4cda-847a-d117545fd6ef
-- title:
--   CCS: proj R insert
-- statement:
--   The CCS construction uses the proj R insert property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/CCS/Par.lean#L319-L332
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/CCS/Par.lean#L319-L332

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

theorem CCS.projR_insert {t : Tag E F} {y : F.Event} (hy : t.evR = some y) :
    projR (c ∪ {t}) = projR c ∪ {y} := by sorry
