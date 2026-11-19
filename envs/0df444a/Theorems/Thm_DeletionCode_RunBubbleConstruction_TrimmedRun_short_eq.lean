-- Prove2me | Theorems.Thm_DeletionCode_RunBubbleConstruction_TrimmedRun_short_eq
-- name    : DeletionCode.RunBubbleConstruction.TrimmedRun.short_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:24:14.951148+00:00
-- url     : https://prove2.me/theorems/ee699a25-5a4e-490d-9eaf-a9a211a7e545
-- title:
--   Trimmed Run: short eq
-- statement:
--   The Trimmed Run construction uses the short eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/RunBubbleConstruction.lean#L88-L97
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/RunBubbleConstruction.lean#L88-L97

import Definitions.Def_DeletionCode_MaximalRuns
import Definitions.Def_DeletionCode_RunBubbleConstruction
set_option autoImplicit true
open DeletionCode DeletionCode.RunBubbleConstruction
open Windows HeaderRecovery CatalogueWords MaximalRuns
open DeletionCode.RunBubbleConstruction.TrimmedRun
variable {k rho : ℕ} {pre suffix : List Bool} {bit : Bool} {orientation : Orientation}

theorem DeletionCode.RunBubbleConstruction.TrimmedRun.short_eq (r : TrimmedRun k pre suffix rho bit orientation) :
    pre ++ List.replicate (rho - 1) bit ++ suffix =
      r.before ++ r.bubble.shortWord ++ r.after := by sorry
