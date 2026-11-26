-- Prove2me | Theorems.Thm_FD1D_LocalHazard_qR_eq_count_mul_hR
-- name    : FD1D.LocalHazard.qR_eq_count_mul_hR
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:57:20.437813+00:00
-- url     : https://prove2.me/theorems/9f2a0d7f-fa6e-47ae-aa6b-9ef4b96e2cb5
-- title:
--   Local Hazard: q R eq count mul h R
-- statement:
--   The Local Hazard construction uses the q R eq count mul h R property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Hazard.lean#L158-L160
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Hazard.lean#L158-L160

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Hazard
set_option autoImplicit true
open FD1D
noncomputable section
open FD1D.LocalHazard

theorem FD1D.LocalHazard.qR_eq_count_mul_hR {a h : ℝ} {x y : ℕ} (ha : 0 < a) :
    qR a h x y = (y : ℝ) * hR a h x y := by sorry
