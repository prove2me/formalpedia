-- Prove2me | Theorems.Thm_FD1D_stationary_cost_le_six
-- name    : FD1D.stationary_cost_le_six
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:33:15.484242+00:00
-- url     : https://prove2.me/theorems/369fbf28-ef65-4ed8-9787-8343f3bb8610
-- title:
--   FD1 D: stationary cost le six
-- statement:
--   Equation (3) plus the hazard bound implies the advertised stationary cost.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Arithmetic.lean#L43-L65
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Arithmetic.lean#L43-L65

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Arithmetic
set_option autoImplicit true
open FD1D
noncomputable section

theorem FD1D.stationary_cost_le_six
    {a m H cell cost : ℝ}
    (ha : 0 ≤ a) (hm : 0 < m)
    (hcell : cell ≤ 2 * a / m)
    (hH0 : 1 / m ^ 2 ≤ H)
    (hH : H ≤ 206 / (3 * m ^ 2))
    (hcost :
      cost ≤ cell +
        a / Real.sqrt 6 * Real.sqrt (H - 1 / m ^ 2)) :
    cost ≤ 6 * a / m := by sorry
