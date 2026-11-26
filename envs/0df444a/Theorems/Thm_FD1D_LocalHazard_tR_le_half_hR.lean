-- Prove2me | Theorems.Thm_FD1D_LocalHazard_tR_le_half_hR
-- name    : FD1D.LocalHazard.tR_le_half_hR
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:55:29.551509+00:00
-- url     : https://prove2.me/theorems/d86d0088-2f5f-505e-8c42-eff8becbe1e2
-- title:
--   Local Hazard: t R le half h R
-- statement:
--   The Local Hazard construction uses the t R le half h R property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Hazard.lean#L429-L439
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Hazard.lean#L429-L439

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Hazard
set_option autoImplicit true
open FD1D
noncomputable section
open FD1D.LocalHazard

theorem FD1D.LocalHazard.tR_le_half_hR {a p h : ℝ} {x y : ℕ}
    (ha : 0 < a) (hh : 0 ≤ h) (ht : t a p h x y ≤ h / 2) :
    tR a p h x y ≤ hR a h x y / 2 := by sorry
