-- Prove2me | Theorems.Thm_FD1D_LocalHazard_tL_eq
-- name    : FD1D.LocalHazard.tL_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:55:06.070196+00:00
-- url     : https://prove2.me/theorems/baef52cd-7ca8-5af0-a3df-d47d43d9b7c5
-- title:
--   Local Hazard: t L eq
-- statement:
--   The left relation `t_L = t/2 + w` from equation (4).
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Hazard.lean#L401-L408
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Hazard.lean#L401-L408

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Hazard
set_option autoImplicit true
open FD1D
noncomputable section
open FD1D.LocalHazard

theorem FD1D.LocalHazard.tL_eq {a p h : ℝ} {x y : ℕ} (ha : 0 < a) :
    tL a p h x y = t a p h x y / 2 + w a h x y := by sorry
