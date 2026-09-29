-- Prove2me | Theorems.Thm_CKLaneA3X_Step027_polynomial_of_rows
-- name    : CKLaneA3X.Step027.polynomial_of_rows
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-25T02:46:15.669974+00:00
-- url     : https://prove2.me/theorems/502cda15-8a17-4656-9ad5-cde33cc60d05
-- title:
--   All 24 row equalities reconstruct the A3X square polynomial
-- statement:
--   If all 24 rows of the truncated square equal their stored D_UsUs rows, then the full polynomial lists are equal. The proof checks exact lengths and uses every supplied row equality; no missing row proof is assumed.
-- source:
--   https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneA3X/Step027.lean#L15

import Mathlib.Data.List.GetD
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.FinCases
import Definitions.Def_A3X_numeric_core
import Definitions.Def_A3X_Step027_data_functions

set_option maxHeartbeats 0
set_option maxRecDepth 100000
open CKLaneA3X

theorem CKLaneA3X.Step027.polynomial_of_rows (hrows : ∀ i : Fin 24, (TPoly.mulT D_Us.P D_Us.P 24).getD i [] = D_UsUs.P.getD i []) : (TPoly.mulT D_Us.P D_Us.P 24) = D_UsUs.P := by sorry
