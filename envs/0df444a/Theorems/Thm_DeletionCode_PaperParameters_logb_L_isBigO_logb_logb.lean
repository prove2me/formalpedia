-- Prove2me | Theorems.Thm_DeletionCode_PaperParameters_logb_L_isBigO_logb_logb
-- name    : DeletionCode.PaperParameters.logb_L_isBigO_logb_logb
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:17:25.723152+00:00
-- url     : https://prove2.me/theorems/fc76407f-be65-4411-a4a9-c532b46dd49f
-- title:
--   Paper Parameters: logb L is Big O logb logb
-- statement:
--   The Paper Parameters construction uses the logb L is Big O logb logb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/PaperParameters.lean#L139-L150
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/PaperParameters.lean#L139-L150

import Definitions.Def_DeletionCode_UniqueWordParameters
import Definitions.Def_DeletionCode_HeaderRecovery
import Mathlib.Analysis.Asymptotics.Defs
import Definitions.Def_DeletionCode_PaperParameters
set_option autoImplicit true
open DeletionCode DeletionCode.PaperParameters
open Filter Asymptotics
open scoped Topology

theorem DeletionCode.PaperParameters.logb_L_isBigO_logb_logb :
    (fun n : ℕ => Real.logb 2 (L n : ℝ)) =O[atTop]
      (fun n => Real.logb 2 (Real.logb 2 (n : ℝ))) := by sorry
