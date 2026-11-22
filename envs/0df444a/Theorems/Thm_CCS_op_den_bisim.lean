-- Prove2me | Theorems.Thm_CCS_op_den_bisim
-- name    : CCS.op_den_bisim
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T21:11:33.778922+00:00
-- url     : https://prove2.me/theorems/27e508b8-93db-4e14-8285-afc578fdd24f
-- title:
--   CCS: op den bisim
-- statement:
--   Coincidence of the two semantics, via the residual process.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/CCS/Bisimulation.lean#L341-L349
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/CCS/Bisimulation.lean#L341-L349

import Definitions.Def_EventStructures_LTS_Basic
import Definitions.Def_EventStructures_CCS_Semantics
import Definitions.Def_EventStructures_CCS_Bisimulation
set_option autoImplicit true
open CCS ConfFamily
open CCS
universe u
variable {Name : Type u}

theorem CCS.op_den_bisim (P : Process Name) : Bisimilar (opLTSI P) (denLTSI P) := by sorry
