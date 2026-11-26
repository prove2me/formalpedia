-- Prove2me | Theorems.Thm_FD1D_LocalHazard_q_mul_dR_eq_count_mul_hR
-- name    : FD1D.LocalHazard.q_mul_dR_eq_count_mul_hR
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:54:00.655991+00:00
-- url     : https://prove2.me/theorems/e68cb579-a549-4fff-8e5a-c151bc4db386
-- title:
--   Local Hazard: q mul d R eq count mul h R
-- statement:
--   Algebraic propagation of `q = N h` to the right child.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Hazard.lean#L140-L152
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Hazard.lean#L140-L152

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Hazard
set_option autoImplicit true
open FD1D
noncomputable section
open FD1D.LocalHazard

theorem FD1D.LocalHazard.q_mul_dR_eq_count_mul_hR {a h qParent : ℝ} {x y : ℕ}
    (ha : 0 < a) (hq : qParent = N x y * h) :
    qParent * dR a x y = (y : ℝ) * hR a h x y := by sorry
