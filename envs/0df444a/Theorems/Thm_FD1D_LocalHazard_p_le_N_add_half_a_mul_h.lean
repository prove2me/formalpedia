-- Prove2me | Theorems.Thm_FD1D_LocalHazard_p_le_N_add_half_a_mul_h
-- name    : FD1D.LocalHazard.p_le_N_add_half_a_mul_h
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:55:37.220063+00:00
-- url     : https://prove2.me/theorems/4407cf6c-4d4f-5059-97ff-9ddd063adb73
-- title:
--   Local Hazard: p le N add half a mul h
-- statement:
--   The sharper first inequality used in equation (5).
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Hazard.lean#L466-L472
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Hazard.lean#L466-L472

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Hazard
set_option autoImplicit true
open FD1D
noncomputable section
open FD1D.LocalHazard

theorem FD1D.LocalHazard.p_le_N_add_half_a_mul_h {a p h : ℝ} {x y : ℕ}
    (ha : 0 < a) (ht : t a p h x y ≤ h / 2) :
    p ≤ (N x y + a / 2) * h := by sorry
