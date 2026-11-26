-- Prove2me | Theorems.Thm_FD1D_LocalHazard_hR_pos
-- name    : FD1D.LocalHazard.hR_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:54:14.534929+00:00
-- url     : https://prove2.me/theorems/50811ca2-fb10-48f1-abd7-d3232d30d87f
-- title:
--   Local Hazard: h R pos
-- statement:
--   The Local Hazard construction uses the h R pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Hazard.lean#L172-L180
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Hazard.lean#L172-L180

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Hazard
set_option autoImplicit true
open FD1D
noncomputable section
open FD1D.LocalHazard

theorem FD1D.LocalHazard.hR_pos {a h : ℝ} {x y : ℕ} (ha : 0 < a) (hh : 0 < h) :
    0 < hR a h x y := by sorry
