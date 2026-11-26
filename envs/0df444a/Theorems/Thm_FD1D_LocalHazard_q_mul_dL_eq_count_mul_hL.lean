-- Prove2me | Theorems.Thm_FD1D_LocalHazard_q_mul_dL_eq_count_mul_hL
-- name    : FD1D.LocalHazard.q_mul_dL_eq_count_mul_hL
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:54:20.289965+00:00
-- url     : https://prove2.me/theorems/57938e24-ebbd-4ea9-b828-dd2f78955cc6
-- title:
--   Local Hazard: q mul d L eq count mul h L
-- statement:
--   Algebraic propagation of `q = N h` to the left child.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Hazard.lean#L125-L137
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Hazard.lean#L125-L137

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Hazard
set_option autoImplicit true
open FD1D
noncomputable section
open FD1D.LocalHazard

theorem FD1D.LocalHazard.q_mul_dL_eq_count_mul_hL {a h qParent : ℝ} {x y : ℕ}
    (ha : 0 < a) (hq : qParent = N x y * h) :
    qParent * dL a x y = (x : ℝ) * hL a h x y := by sorry
