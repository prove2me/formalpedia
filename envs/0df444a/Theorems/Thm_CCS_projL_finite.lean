-- Prove2me | Theorems.Thm_CCS_projL_finite
-- name    : CCS.projL_finite
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T21:10:30.830813+00:00
-- url     : https://prove2.me/theorems/37f26c72-127e-4331-b85a-4cb3d93222de
-- title:
--   CCS: proj L finite
-- statement:
--   The CCS construction uses the proj L finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/CCS/Par.lean#L99-L108
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/CCS/Par.lean#L99-L108

import Definitions.Def_EventStructures_General_Stable
import Definitions.Def_EventStructures_Stable_Basic
import Definitions.Def_EventStructures_CCS_Syntax
import Definitions.Def_EventStructures_CCS_Par
set_option autoImplicit true
open GES
open CCS
variable {Name : Type*}
variable {E F : SES (Action Name)}

theorem CCS.projL_finite {C : Set (Tag E F)} (h : C.Finite) : (projL C).Finite := by sorry
