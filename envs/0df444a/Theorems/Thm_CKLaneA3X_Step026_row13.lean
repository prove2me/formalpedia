-- Prove2me | Theorems.Thm_CKLaneA3X_Step026_row13
-- name    : CKLaneA3X.Step026.row13
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-25T00:57:11.018801+00:00
-- url     : https://prove2.me/theorems/b3eed16b-ebe5-436e-a22b-5783b7d456cb
-- title:
--   A3X product row 13 matches its stored certificate
-- statement:
--   Output row 13 of the exact A3X product truncated to 24 rows equals the complete stored row of D_mInner, including every sparse key and Laurent coefficient. The stored row has 16 sparse entries and 127 Laurent monomials. This newly generated row certificate leaves all other rows and the original analytic validity statement separate.
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

theorem CKLaneA3X.Step026.row13 : (TPoly.mulT D_m.P D_inner.P 24).getD 13 [] = D_mInner.P.getD 13 [] := by sorry
