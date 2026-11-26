-- Prove2me | Theorems.Thm_FD1D_LocalHazard_V_eq
-- name    : FD1D.LocalHazard.V_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:51:58.579305+00:00
-- url     : https://prove2.me/theorems/5a8289ca-0d5c-5cb7-9888-09d5fcf952b4
-- title:
--   Local Hazard: V eq
-- statement:
--   The Local Hazard construction uses the V eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Hazard.lean#L267-L280
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Hazard.lean#L267-L280

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Hazard
set_option autoImplicit true
open FD1D
noncomputable section
open FD1D.LocalHazard

theorem FD1D.LocalHazard.V_eq {a h : ℝ} {x y : ℕ} (ha : 0 < a) :
    V a h x y =
      h * ((x : ℝ) - (y : ℝ)) ^ 2 / (2 * D a x y) := by sorry
