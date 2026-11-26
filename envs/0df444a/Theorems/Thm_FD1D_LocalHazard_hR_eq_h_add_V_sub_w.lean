-- Prove2me | Theorems.Thm_FD1D_LocalHazard_hR_eq_h_add_V_sub_w
-- name    : FD1D.LocalHazard.hR_eq_h_add_V_sub_w
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:54:57.510773+00:00
-- url     : https://prove2.me/theorems/ed4a20fc-b1c9-4eae-984c-d5ff6e16f703
-- title:
--   Local Hazard: h R eq h add V sub w
-- statement:
--   The Local Hazard construction uses the h R eq h add V sub w property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Hazard.lean#L262-L265
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Hazard.lean#L262-L265

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Hazard
set_option autoImplicit true
open FD1D
noncomputable section
open FD1D.LocalHazard

theorem FD1D.LocalHazard.hR_eq_h_add_V_sub_w (a h : ℝ) (x y : ℕ) :
    hR a h x y = h + V a h x y - w a h x y := by sorry
