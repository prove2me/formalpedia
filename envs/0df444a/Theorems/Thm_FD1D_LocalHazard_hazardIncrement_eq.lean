-- Prove2me | Theorems.Thm_FD1D_LocalHazard_hazardIncrement_eq
-- name    : FD1D.LocalHazard.hazardIncrement_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:54:30.822038+00:00
-- url     : https://prove2.me/theorems/f25a62eb-8d1c-5044-a20f-f3a64d107b31
-- title:
--   Local Hazard: hazard Increment eq
-- statement:
--   The exact identity in equation (1).
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Hazard.lean#L214-L230
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Hazard.lean#L214-L230

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Hazard
set_option autoImplicit true
open FD1D
noncomputable section
open FD1D.LocalHazard

theorem FD1D.LocalHazard.hazardIncrement_eq {a h : ℝ} {x y : ℕ} (ha : 0 < a) :
    (hL a h x y ^ 2 + hR a h x y ^ 2) / 2 - h ^ 2 =
      b a h x y ^ 2 / a ^ 2 *
        ((3 - rho x y ^ 2) / 4 + a / N x y) := by sorry
