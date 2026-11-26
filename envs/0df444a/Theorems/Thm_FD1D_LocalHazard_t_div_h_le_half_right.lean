-- Prove2me | Theorems.Thm_FD1D_LocalHazard_t_div_h_le_half_right
-- name    : FD1D.LocalHazard.t_div_h_le_half_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:59:24.139828+00:00
-- url     : https://prove2.me/theorems/42275edb-c10b-4565-9ff3-f78c6f536484
-- title:
--   Local Hazard: t div h le half right
-- statement:
--   Propagation of the invariant `t/h ≤ 1/2` to the right child.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Hazard.lean#L454-L463
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Hazard.lean#L454-L463

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Hazard
set_option autoImplicit true
open FD1D
noncomputable section
open FD1D.LocalHazard

theorem FD1D.LocalHazard.t_div_h_le_half_right {a p h : ℝ} {x y : ℕ}
    (ha : 0 < a) (hh : 0 < h) (ht : t a p h x y / h ≤ 1 / 2) :
    tR a p h x y / hR a h x y ≤ 1 / 2 := by sorry
