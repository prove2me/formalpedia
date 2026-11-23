-- Prove2me | Theorems.Thm_Comp_HideOrRunData_hrd_lw
-- name    : Comp.HideOrRunData.hrd_lw
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T00:17:49.266268+00:00
-- url     : https://prove2.me/theorems/24d4021d-be11-403e-8d29-5b800dd92515
-- title:
--   Hide Or Run Data: hrd lw
-- statement:
--   The Hide Or Run Data construction uses the hrd lw property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/HideOrRunDataQ.lean#L131-L134
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/HideOrRunDataQ.lean#L131-L134

import Definitions.Def_Comp_ModelDataQualitative
import Definitions.Def_Comp_HideOrRunDataQ
set_option autoImplicit true
set_option linter.hashCommand false
open Comp
open Comp.HideOrRunData

theorem Comp.HideOrRunData.hrd_lw : ∀ (x y : Finset (Fin hrd.nStates)) (s : Fin hrd.nStates),
    hrd.lStepOf hrd_shape x y s ((hrd.lStepOf hrd_shape x y s)^[2] ∅)
      = (hrd.lStepOf hrd_shape x y s)^[2] ∅ := by sorry
