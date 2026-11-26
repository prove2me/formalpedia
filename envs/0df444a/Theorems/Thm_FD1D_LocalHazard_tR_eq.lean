-- Prove2me | Theorems.Thm_FD1D_LocalHazard_tR_eq
-- name    : FD1D.LocalHazard.tR_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:55:20.912657+00:00
-- url     : https://prove2.me/theorems/921160ba-9cb5-4985-a9dd-1f38f41d2d9f
-- title:
--   Local Hazard: t R eq
-- statement:
--   The right relation `t_R = t/2 - w` from equation (4).
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Hazard.lean#L411-L418
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Hazard.lean#L411-L418

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Hazard
set_option autoImplicit true
open FD1D
noncomputable section
open FD1D.LocalHazard

theorem FD1D.LocalHazard.tR_eq {a p h : ℝ} {x y : ℕ} (ha : 0 < a) :
    tR a p h x y = t a p h x y / 2 - w a h x y := by sorry
