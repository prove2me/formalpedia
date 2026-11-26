-- Prove2me | Theorems.Thm_FD1D_LocalHazard_V_div_h_le
-- name    : FD1D.LocalHazard.V_div_h_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:58:52.188812+00:00
-- url     : https://prove2.me/theorems/b38d033d-5090-4240-925a-0efdc7d93d32
-- title:
--   Local Hazard: V div h le
-- statement:
--   The bound `V/h ≤ N/(2a)` from equation (4).
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Hazard.lean#L343-L346
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Hazard.lean#L343-L346

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Hazard
set_option autoImplicit true
open FD1D
noncomputable section
open FD1D.LocalHazard

theorem FD1D.LocalHazard.V_div_h_le {a h : ℝ} {x y : ℕ} (ha : 0 < a) (hh : 0 < h) :
    V a h x y / h ≤ N x y / (2 * a) := by sorry
