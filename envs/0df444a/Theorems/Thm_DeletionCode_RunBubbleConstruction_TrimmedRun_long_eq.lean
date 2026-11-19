-- Prove2me | Theorems.Thm_DeletionCode_RunBubbleConstruction_TrimmedRun_long_eq
-- name    : DeletionCode.RunBubbleConstruction.TrimmedRun.long_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:24:01.340459+00:00
-- url     : https://prove2.me/theorems/cbc11da8-7456-4e0c-b163-996c92695b7e
-- title:
--   Trimmed Run: long eq
-- statement:
--   The Trimmed Run construction uses the long eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/RunBubbleConstruction.lean#L77-L86
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/RunBubbleConstruction.lean#L77-L86

import Definitions.Def_DeletionCode_MaximalRuns
import Definitions.Def_DeletionCode_RunBubbleConstruction
set_option autoImplicit true
open DeletionCode DeletionCode.RunBubbleConstruction
open Windows HeaderRecovery CatalogueWords MaximalRuns
open DeletionCode.RunBubbleConstruction.TrimmedRun
variable {k rho : ℕ} {pre suffix : List Bool} {bit : Bool} {orientation : Orientation}

theorem DeletionCode.RunBubbleConstruction.TrimmedRun.long_eq (r : TrimmedRun k pre suffix rho bit orientation) :
    pre ++ List.replicate rho bit ++ suffix =
      r.before ++ r.bubble.longWord ++ r.after := by sorry
