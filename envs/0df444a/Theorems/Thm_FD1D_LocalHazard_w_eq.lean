-- Prove2me | Theorems.Thm_FD1D_LocalHazard_w_eq
-- name    : FD1D.LocalHazard.w_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:54:50.103955+00:00
-- url     : https://prove2.me/theorems/b7166240-36a6-4958-a8df-7b34e5539671
-- title:
--   Local Hazard: w eq
-- statement:
--   The Local Hazard construction uses the w eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Hazard.lean#L282-L294
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Hazard.lean#L282-L294

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Hazard
set_option autoImplicit true
open FD1D
noncomputable section
open FD1D.LocalHazard

theorem FD1D.LocalHazard.w_eq {a h : ℝ} {x y : ℕ} (ha : 0 < a) :
    w a h x y =
      h * N x y * ((y : ℝ) - (x : ℝ)) / (2 * D a x y) := by sorry
