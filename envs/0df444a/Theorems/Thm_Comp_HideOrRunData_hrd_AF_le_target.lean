-- Prove2me | Theorems.Thm_Comp_HideOrRunData_hrd_AF_le_target
-- name    : Comp.HideOrRunData.hrd_AF_le_target
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T00:46:58.166348+00:00
-- url     : https://prove2.me/theorems/78bf4b1f-7e14-4a95-8808-abfdef229b7a
-- title:
--   Hide Or Run Data: hrd AF le target
-- statement:
--   Second outer step: and here they part. Restricted to the row actions safe for `{0, 1}`, the
--       runner can only wait, and waiting against a wait returns to the stand-off.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/HideOrRunDataQ.lean#L183-L186
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/HideOrRunDataQ.lean#L183-L186

import Definitions.Def_Comp_ModelDataQualitative
import Definitions.Def_Comp_HideOrRunDataQ
set_option autoImplicit true
set_option linter.hashCommand false
open Comp
open Comp.HideOrRunData

theorem Comp.HideOrRunData.hrd_AF_le_target : (hrd.toCsgQ.toCSG hrd_wf).AF ↑hrdTarget
    ≤ (↑hrdTarget : Set (Fin hrd.nStates)) := by sorry
