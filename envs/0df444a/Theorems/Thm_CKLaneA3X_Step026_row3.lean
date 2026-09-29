-- Prove2me | Theorems.Thm_CKLaneA3X_Step026_row3
-- name    : CKLaneA3X.Step026.row3
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-25T00:57:11.582621+00:00
-- url     : https://prove2.me/theorems/60be3d66-72f1-4192-81ca-b20fb9b8521f
-- title:
--   A3X product row 3 matches its stored certificate
-- statement:
--   Output row 3 of the exact A3X product truncated to 24 rows equals the complete stored row of D_mInner, including every sparse key and Laurent coefficient. The stored row has 2 sparse entries and 6 Laurent monomials. This newly generated row certificate leaves all other rows and the original analytic validity statement separate.
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

theorem CKLaneA3X.Step026.row3 : (TPoly.mulT D_m.P D_inner.P 24).getD 3 [] = D_mInner.P.getD 3 [] := by sorry
