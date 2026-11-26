-- Prove2me | Theorems.Thm_FD1D_LocalHazard_count_add_a_pos
-- name    : FD1D.LocalHazard.count_add_a_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:52:17.510589+00:00
-- url     : https://prove2.me/theorems/fab99323-9730-5083-b838-13ae312fd307
-- title:
--   Local Hazard: count add a pos
-- statement:
--   The Local Hazard construction uses the count add a pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Hazard.lean#L86-L87
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Hazard.lean#L86-L87

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Hazard
set_option autoImplicit true
open FD1D
noncomputable section
open FD1D.LocalHazard

theorem FD1D.LocalHazard.count_add_a_pos {a : ℝ} (ha : 0 < a) (k : ℕ) : 0 < (k : ℝ) + a := by sorry
