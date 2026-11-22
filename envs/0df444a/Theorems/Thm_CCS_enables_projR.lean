-- Prove2me | Theorems.Thm_CCS_enables_projR
-- name    : CCS.enables_projR
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:52:39.222887+00:00
-- url     : https://prove2.me/theorems/f17eea60-5626-4223-93c7-00d806395554
-- title:
--   CCS: enables proj R
-- statement:
--   The CCS construction uses the enables proj R property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/CCS/Par.lean#L366-L382
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/CCS/Par.lean#L366-L382

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

theorem CCS.enables_projR {t : Tag E F} {y : F.Event}
    (hins : (parSES E F).toGES.isConf (c ∪ {t}))
    (hfr : t ∉ c) (hy : t.evR = some y) :
    F.toGES.isConf (projR c ∪ {y}) ∧ y ∉ projR c := by sorry
