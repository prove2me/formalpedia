-- Prove2me | Theorems.Thm_FD1D_LocalHazard_tL_le_half_hL
-- name    : FD1D.LocalHazard.tL_le_half_hL
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:55:38.445054+00:00
-- url     : https://prove2.me/theorems/f112c50c-d981-44e7-b09a-a7ca9335cf70
-- title:
--   Local Hazard: t L le half h L
-- statement:
--   The Local Hazard construction uses the t L le half h L property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Hazard.lean#L420-L427
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Hazard.lean#L420-L427

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Hazard
set_option autoImplicit true
open FD1D
noncomputable section
open FD1D.LocalHazard

theorem FD1D.LocalHazard.tL_le_half_hL {a p h : ℝ} {x y : ℕ}
    (ha : 0 < a) (hh : 0 ≤ h) (ht : t a p h x y ≤ h / 2) :
    tL a p h x y ≤ hL a h x y / 2 := by sorry
