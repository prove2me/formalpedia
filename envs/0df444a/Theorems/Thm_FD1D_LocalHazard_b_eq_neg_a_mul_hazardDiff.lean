-- Prove2me | Theorems.Thm_FD1D_LocalHazard_b_eq_neg_a_mul_hazardDiff
-- name    : FD1D.LocalHazard.b_eq_neg_a_mul_hazardDiff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:54:27.499605+00:00
-- url     : https://prove2.me/theorems/ab9dd486-7e7b-552e-abd1-e2ea99acef8f
-- title:
--   Local Hazard: b eq neg a mul hazard Diff
-- statement:
--   Equation `b = -a(h_L-h_R)`, including the empty-node extension.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Hazard.lean#L183-L194
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Hazard.lean#L183-L194

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Hazard
set_option autoImplicit true
open FD1D
noncomputable section
open FD1D.LocalHazard

theorem FD1D.LocalHazard.b_eq_neg_a_mul_hazardDiff {a h : ℝ} {x y : ℕ} (ha : 0 < a) :
    b a h x y = -a * (hL a h x y - hR a h x y) := by sorry
