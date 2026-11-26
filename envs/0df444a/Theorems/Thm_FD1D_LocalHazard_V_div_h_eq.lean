-- Prove2me | Theorems.Thm_FD1D_LocalHazard_V_div_h_eq
-- name    : FD1D.LocalHazard.V_div_h_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:55:09.469424+00:00
-- url     : https://prove2.me/theorems/3ebc5d32-cb92-4e42-a088-5df62dc00e6d
-- title:
--   Local Hazard: V div h eq
-- statement:
--   The Local Hazard construction uses the V div h eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Hazard.lean#L336-L340
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Hazard.lean#L336-L340

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Hazard
set_option autoImplicit true
open FD1D
noncomputable section
open FD1D.LocalHazard

theorem FD1D.LocalHazard.V_div_h_eq {a h : ℝ} {x y : ℕ} (ha : 0 < a) (hh : 0 < h) :
    V a h x y / h =
      ((x : ℝ) - (y : ℝ)) ^ 2 / (2 * D a x y) := by sorry
