-- Prove2me | Theorems.Thm_CKLaneA3X_Step026_row23_sigma25
-- name    : CKLaneA3X.Step026.row23_sigma25
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-24T23:54:53.070705+00:00
-- url     : https://prove2.me/theorems/aa9189d0-50a7-4604-b94c-2bd55166599f
-- title:
--   A3X output row 23, slot 25 Laurent coefficient block
-- statement:
--   Let $P_m$, $P_{\mathrm{inner}}$, and $P_{m\mathrm{Inner}}$ be the exact rational coefficient arrays in the original A3X Taylor-model data. In zero-based output row 23, the Laurent-polynomial list at sparse slot 25 of the product truncated to 24 rows equals the stored list at that slot in $P_{m\mathrm{Inner}}$. The stored list has 13 Laurent entries and its stored sigma exponent is 25. The theorem compares the Laurent lists; the equality of sparse keys, reconstruction of the complete row, other rows, and the remainder inequality are separate obligations. This is a new computed fragment of the polynomial equality required by Step026.
-- source:
--   https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneA3X/Step026.lean#L15

import Definitions.Def_A3X_numeric_core
import Definitions.Def_A3X_Step026_data

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open CKLaneA3X

theorem CKLaneA3X.Step026.row23_sigma25 : (((TPoly.mulT D_m.P D_inner.P 24).getD 23 []).getD 25 (0, [])).2 = ((D_mInner.P.getD 23 []).getD 25 (0, [])).2 := by sorry
