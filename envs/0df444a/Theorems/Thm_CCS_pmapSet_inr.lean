-- Prove2me | Theorems.Thm_CCS_pmapSet_inr
-- name    : CCS.pmapSet_inr
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:54:48.906738+00:00
-- url     : https://prove2.me/theorems/d49874e0-d1ed-4b33-b737-7048b9e8e153
-- title:
--   CCS: pmap Set inr
-- statement:
--   The CCS construction uses the pmap Set inr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/CCS/Semantics.lean#L229-L236
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/CCS/Semantics.lean#L229-L236

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

theorem CCS.pmapSet_inr (s : Set (E.Event ⊕ F.Event)) :
    GES.pmapSet (G := (sum E F).toGES) (H := F.toGES) Sum.getRight? s
      = {z | Sum.inr z ∈ s} := by sorry
