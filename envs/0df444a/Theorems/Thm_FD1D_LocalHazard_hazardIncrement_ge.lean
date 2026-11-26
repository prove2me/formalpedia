-- Prove2me | Theorems.Thm_FD1D_LocalHazard_hazardIncrement_ge
-- name    : FD1D.LocalHazard.hazardIncrement_ge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:57:51.766795+00:00
-- url     : https://prove2.me/theorems/56763eac-3bf4-5c47-b364-fa4d7e6293d7
-- title:
--   Local Hazard: hazard Increment ge
-- statement:
--   The lower bound in equation (1).
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Hazard.lean#L233-L255
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Hazard.lean#L233-L255

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Hazard
set_option autoImplicit true
open FD1D
noncomputable section
open FD1D.LocalHazard

theorem FD1D.LocalHazard.hazardIncrement_ge {a h : ℝ} {x y : ℕ} (ha : 0 < a) :
    b a h x y ^ 2 / (2 * a ^ 2) ≤
      (hL a h x y ^ 2 + hR a h x y ^ 2) / 2 - h ^ 2 := by sorry
