-- Prove2me | Theorems.Thm_FD1D_transient_cost_le_six
-- name    : FD1D.transient_cost_le_six
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:33:16.598008+00:00
-- url     : https://prove2.me/theorems/d7794a96-8ef1-5d14-8cc9-bf62e247be5f
-- title:
--   FD1 D: transient cost le six
-- statement:
--   The FD1 D construction uses the transient cost le six property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Arithmetic.lean#L92-L114
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Arithmetic.lean#L92-L114

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Arithmetic
set_option autoImplicit true
open FD1D
noncomputable section

theorem FD1D.transient_cost_le_six
    {a m T H cell cost : ℝ}
    (ha : 0 ≤ a) (hm : 0 < m) (hT : m ^ 2 ≤ T)
    (hcell : cell ≤ 2 * a / m)
    (hH0 : 1 / m ^ 2 ≤ H)
    (hH : H ≤ 206 / (3 * m ^ 2) + 1 / T)
    (hcost :
      cost ≤ cell +
        a / Real.sqrt 6 * Real.sqrt (H - 1 / m ^ 2)) :
    cost ≤ 6 * a / m := by sorry
