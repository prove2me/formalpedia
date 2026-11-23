-- Prove2me | Theorems.Thm_Comp_HideOrRunData_hrd_nonneg
-- name    : Comp.HideOrRunData.hrd_nonneg
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T00:46:48.002859+00:00
-- url     : https://prove2.me/theorems/e848a842-0958-4104-a71d-d67e87947b42
-- title:
--   Hide Or Run Data: hrd nonneg
-- statement:
--   The Hide Or Run Data construction uses the hrd nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/HideOrRunDataQ.lean#L84-L88
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/HideOrRunDataQ.lean#L84-L88

import Definitions.Def_Comp_ModelDataQualitative
import Definitions.Def_Comp_HideOrRunDataQ
set_option autoImplicit true
set_option linter.hashCommand false
open Comp
open Comp.HideOrRunData

theorem Comp.HideOrRunData.hrd_nonneg : hrd.Nonneg := by sorry
