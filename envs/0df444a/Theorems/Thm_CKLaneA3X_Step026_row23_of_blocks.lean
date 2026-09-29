-- Prove2me | Theorems.Thm_CKLaneA3X_Step026_row23_of_blocks
-- name    : CKLaneA3X.Step026.row23_of_blocks
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-25T00:01:37.960696+00:00
-- url     : https://prove2.me/theorems/2b8b4770-5fab-4f01-aeea-1db4a3e626d2
-- title:
--   The 26 Laurent blocks reconstruct A3X output row 23
-- statement:
--   Assume the Laurent-list equality at every one of the 26 sparse-list positions in output row 23 of the exact truncated A3X product. Then the entire output row equals row 23 of D_mInner. The proof checks the sparse key sequence and length, and reconstructs list equality from the supplied blocks. This is a conditional reconstruction theorem: it proves none of the unprovided block premises.
-- source:
--   https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneA3X/Step026.lean#L15

import Mathlib.Data.List.GetD
import Definitions.Def_A3X_numeric_core
import Definitions.Def_A3X_Step026_data

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open CKLaneA3X

theorem CKLaneA3X.Step026.row23_of_blocks (hblocks : ∀ i : Fin 26,
      (((TPoly.mulT D_m.P D_inner.P 24).getD 23 []).getD i (0, [])).2 =
        ((D_mInner.P.getD 23 []).getD i (0, [])).2) : (TPoly.mulT D_m.P D_inner.P 24).getD 23 [] = D_mInner.P.getD 23 [] := by sorry
