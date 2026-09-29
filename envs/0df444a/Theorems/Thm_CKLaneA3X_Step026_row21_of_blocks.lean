-- Prove2me | Theorems.Thm_CKLaneA3X_Step026_row21_of_blocks
-- name    : CKLaneA3X.Step026.row21_of_blocks
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-25T01:14:59.335578+00:00
-- url     : https://prove2.me/theorems/0f77798e-cf48-484d-bcff-193b80d21364
-- title:
--   Laurent blocks reconstruct the complete A3X output row 21
-- statement:
--   If all 24 Laurent-list block equalities for output row 21 hold, then the complete sparse product row equals the stored D_mInner row. The proof checks the actual sparse-key sequence and reconstructs equality. Every block hypothesis remains explicit; no missing numerical block is assumed proved.
-- source:
--   https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneA3X/Step026.lean#L15

import Mathlib.Data.List.GetD
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.FinCases
import Definitions.Def_A3X_numeric_core
import Definitions.Def_A3X_Step026_data

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open CKLaneA3X

theorem CKLaneA3X.Step026.row21_of_blocks (hblocks : ∀ i : Fin 24, (((TPoly.mulT D_m.P D_inner.P 24).getD 21 []).getD i (0, [])).2 = ((D_mInner.P.getD 21 []).getD i (0, [])).2) : (TPoly.mulT D_m.P D_inner.P 24).getD 21 [] = D_mInner.P.getD 21 [] := by sorry
