-- Prove2me | Theorems.Thm_FD1D_LocalHazard_abs_w_le_V_add_half_h
-- name    : FD1D.LocalHazard.abs_w_le_V_add_half_h
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:52:35.10691+00:00
-- url     : https://prove2.me/theorems/59906516-6e73-43f1-85b4-d375dc8a639e
-- title:
--   Local Hazard: abs w le V add half h
-- statement:
--   The Local Hazard construction uses the abs w le V add half h property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Hazard.lean#L374-L398
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Hazard.lean#L374-L398

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Hazard
set_option autoImplicit true
open FD1D
noncomputable section
open FD1D.LocalHazard

theorem FD1D.LocalHazard.abs_w_le_V_add_half_h {a h : ℝ} {x y : ℕ}
    (ha : 0 < a) (hh : 0 ≤ h) :
    |w a h x y| ≤ V a h x y + h / 2 := by sorry
