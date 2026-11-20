-- Prove2me | Theorems.Thm_DeletionCode_GeneratingBlocks_signedGenerating_iff
-- name    : DeletionCode.GeneratingBlocks.signedGenerating_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:16:12.380803+00:00
-- url     : https://prove2.me/theorems/d7d0e033-4a22-4b88-b998-08cf169befa0
-- title:
--   Generating Blocks: signed Generating iff
-- statement:
--   Existing concrete-family signed generation is exactly this ordered condition.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/GeneratingBlocks.lean#L93-L97
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/GeneratingBlocks.lean#L93-L97

import Definitions.Def_DeletionCode_RuleSetGraph
import Definitions.Def_DeletionCode_GeneratingBlocks
set_option autoImplicit true
open DeletionCode DeletionCode.GeneratingBlocks
open SignedSupport RuleSetGraph

theorem DeletionCode.GeneratingBlocks.signedGenerating_iff {B : Type*} [Fintype B] (F : RootSelection.Family B)
    (x : Windows.Letters) (n L : ℕ) :
    SignedGenerating F x n L ↔
      Generating (wordSpectrum x n L)
        (fun i : ℕ => ruleSpectrum F L (ruleBubbles F i)) id := by sorry
