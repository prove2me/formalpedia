-- Prove2me | Theorems.Thm_CKLaneA3X_Step026_empty_rows
-- name    : CKLaneA3X.Step026.empty_rows
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-25T00:57:12.011113+00:00
-- url     : https://prove2.me/theorems/decaac28-db23-43b9-a8d4-36f77d45f247
-- title:
--   All 13 empty A3X output rows match their certificates
-- statement:
--   For each of the explicit row indices 0,1,2,4,6,8,10,12,14,16,18,20,22, the exact truncated product row equals the stored empty D_mInner row. Each actual product row is kernel-checked; emptiness is not inferred only from the stored result. The other 11 rows remain separate obligations.
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

theorem CKLaneA3X.Step026.empty_rows (i : Fin 13) : (TPoly.mulT D_m.P D_inner.P 24).getD (([0, 1, 2, 4, 6, 8, 10, 12, 14, 16, 18, 20, 22] : List Nat).getD i 0) [] = D_mInner.P.getD (([0, 1, 2, 4, 6, 8, 10, 12, 14, 16, 18, 20, 22] : List Nat).getD i 0) [] := by sorry
