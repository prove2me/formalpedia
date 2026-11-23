-- Prove2me | Theorems.Thm_Comp_HideOrRunData_hrd_nonzero
-- name    : Comp.HideOrRunData.hrd_nonzero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T00:17:50.624799+00:00
-- url     : https://prove2.me/theorems/1dd8ad12-57ea-42a7-9606-a70a794a2b31
-- title:
--   Hide Or Run Data: hrd nonzero
-- statement:
--   The Hide Or Run Data construction uses the hrd nonzero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/HideOrRunDataQ.lean#L90-L94
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/HideOrRunDataQ.lean#L90-L94

import Definitions.Def_Comp_ModelDataQualitative
import Definitions.Def_Comp_HideOrRunDataQ
set_option autoImplicit true
set_option linter.hashCommand false
open Comp
open Comp.HideOrRunData

theorem Comp.HideOrRunData.hrd_nonzero : hrd.Nonzero := by sorry
