-- Prove2me | Theorems.Thm_FD1D_LocalHazard_t_div_h_le_half_left
-- name    : FD1D.LocalHazard.t_div_h_le_half_left
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:59:17.125823+00:00
-- url     : https://prove2.me/theorems/66397c55-beef-5fde-9cd0-01ecef082994
-- title:
--   Local Hazard: t div h le half left
-- statement:
--   Propagation of the invariant `t/h ≤ 1/2` to the left child.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Hazard.lean#L442-L451
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Hazard.lean#L442-L451

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Hazard
set_option autoImplicit true
open FD1D
noncomputable section
open FD1D.LocalHazard

theorem FD1D.LocalHazard.t_div_h_le_half_left {a p h : ℝ} {x y : ℕ}
    (ha : 0 < a) (hh : 0 < h) (ht : t a p h x y / h ≤ 1 / 2) :
    tL a p h x y / hL a h x y ≤ 1 / 2 := by sorry
