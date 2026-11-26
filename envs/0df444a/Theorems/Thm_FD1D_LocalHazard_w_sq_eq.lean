-- Prove2me | Theorems.Thm_FD1D_LocalHazard_w_sq_eq
-- name    : FD1D.LocalHazard.w_sq_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:55:13.706832+00:00
-- url     : https://prove2.me/theorems/7120b47a-a7db-42ef-a610-64595865d02c
-- title:
--   Local Hazard: w sq eq
-- statement:
--   The exact quadratic identity for `w` in equation (4).
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Hazard.lean#L349-L363
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Hazard.lean#L349-L363

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Hazard
set_option autoImplicit true
open FD1D
noncomputable section
open FD1D.LocalHazard

theorem FD1D.LocalHazard.w_sq_eq {a h : ℝ} {x y : ℕ} (ha : 0 < a) :
    w a h x y ^ 2 =
      N x y / (N x y + 2 * a) * V a h x y * (h + V a h x y) := by sorry
