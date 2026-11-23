-- Prove2me | Theorems.Thm_Comp_HideOrRunData_hrd_LF_le
-- name    : Comp.HideOrRunData.hrd_LF_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T00:23:38.144151+00:00
-- url     : https://prove2.me/theorems/48438579-e3bc-4384-a86a-f8f904f5a1e1
-- title:
--   Hide Or Run Data: hrd LF le
-- statement:
--   One outer step: `{0, 1}` bounds `LF` from above. The descent, one step at a time.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/HideOrRunDataQ.lean#L146-L150
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/HideOrRunDataQ.lean#L146-L150

import Definitions.Def_Comp_ModelDataQualitative
import Definitions.Def_Comp_HideOrRunDataQ
set_option autoImplicit true
set_option linter.hashCommand false
open Comp
open Comp.HideOrRunData
set_option maxRecDepth 4000

theorem Comp.HideOrRunData.hrd_LF_le : (hrd.toCsgQ.toCSG hrd_wf).LF ↑hrdTarget
    ≤ (↑hrdWinning : Set (Fin hrd.nStates)) := by sorry
