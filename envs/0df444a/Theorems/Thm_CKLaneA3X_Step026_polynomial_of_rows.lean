-- Prove2me | Theorems.Thm_CKLaneA3X_Step026_polynomial_of_rows
-- name    : CKLaneA3X.Step026.polynomial_of_rows
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-25T00:57:13.518756+00:00
-- url     : https://prove2.me/theorems/1d9fbcbb-ba2f-429c-bb52-751ad28716ca
-- title:
--   All 24 exact rows reconstruct the A3X polynomial certificate
-- statement:
--   If every one of the 24 truncated product rows equals its stored D_mInner row, then the complete list representation of the product equals D_mInner.P. The proof checks the list lengths and applies extensionality. Every row premise remains explicit; this conditional bridge does not supply any missing row proof.
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

theorem CKLaneA3X.Step026.polynomial_of_rows (hrows : ∀ i : Fin 24, (TPoly.mulT D_m.P D_inner.P 24).getD i [] = D_mInner.P.getD i []) : (TPoly.mulT D_m.P D_inner.P 24) = D_mInner.P := by sorry
