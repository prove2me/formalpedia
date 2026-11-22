-- Prove2me | Theorems.Thm_CCS_projR_finite
-- name    : CCS.projR_finite
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T21:10:29.657147+00:00
-- url     : https://prove2.me/theorems/3c8e53f7-1b71-497c-b43d-171013b6f5e0
-- title:
--   CCS: proj R finite
-- statement:
--   The CCS construction uses the proj R finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/CCS/Par.lean#L110-L119
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/CCS/Par.lean#L110-L119

import Definitions.Def_EventStructures_General_Stable
import Definitions.Def_EventStructures_Stable_Basic
import Definitions.Def_EventStructures_CCS_Syntax
import Definitions.Def_EventStructures_CCS_Par
set_option autoImplicit true
open GES
open CCS
variable {Name : Type*}
variable {E F : SES (Action Name)}

theorem CCS.projR_finite {C : Set (Tag E F)} (h : C.Finite) : (projR C).Finite := by sorry
