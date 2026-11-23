-- Prove2me | Theorems.Thm_Comp_HideOrRunData_hrd_AF_le_winning
-- name    : Comp.HideOrRunData.hrd_AF_le_winning
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T00:23:29.723446+00:00
-- url     : https://prove2.me/theorems/be5802d3-646f-4653-bd7b-5b14afa3a35d
-- title:
--   Hide Or Run Data: hrd AF le winning
-- statement:
--   First outer step: the two modes still agree.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/HideOrRunDataQ.lean#L176-L179
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/HideOrRunDataQ.lean#L176-L179

import Definitions.Def_Comp_ModelDataQualitative
import Definitions.Def_Comp_HideOrRunDataQ
set_option autoImplicit true
set_option linter.hashCommand false
open Comp
open Comp.HideOrRunData

theorem Comp.HideOrRunData.hrd_AF_le_winning : (hrd.toCsgQ.toCSG hrd_wf).AF ↑hrdTarget
    ≤ (↑hrdWinning : Set (Fin hrd.nStates)) := by sorry
