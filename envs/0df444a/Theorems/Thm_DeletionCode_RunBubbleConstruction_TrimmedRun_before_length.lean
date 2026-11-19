-- Prove2me | Theorems.Thm_DeletionCode_RunBubbleConstruction_TrimmedRun_before_length
-- name    : DeletionCode.RunBubbleConstruction.TrimmedRun.before_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:24:13.143481+00:00
-- url     : https://prove2.me/theorems/8b07f717-9acb-453b-8b59-056c14eda2b2
-- title:
--   Trimmed Run: before length
-- statement:
--   The Trimmed Run construction uses the before length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/RunBubbleConstruction.lean#L99-L102
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/RunBubbleConstruction.lean#L99-L102

import Definitions.Def_DeletionCode_MaximalRuns
import Definitions.Def_DeletionCode_RunBubbleConstruction
set_option autoImplicit true
open DeletionCode DeletionCode.RunBubbleConstruction
open Windows HeaderRecovery CatalogueWords MaximalRuns
open DeletionCode.RunBubbleConstruction.TrimmedRun
variable {k rho : ℕ} {pre suffix : List Bool} {bit : Bool} {orientation : Orientation}

theorem DeletionCode.RunBubbleConstruction.TrimmedRun.before_length (r : TrimmedRun k pre suffix rho bit orientation) :
    r.before.length + (windowLength k - rho) = pre.length := by sorry
