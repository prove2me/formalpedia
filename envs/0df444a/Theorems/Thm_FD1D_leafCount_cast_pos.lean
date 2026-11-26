-- Prove2me | Theorems.Thm_FD1D_leafCount_cast_pos
-- name    : FD1D.leafCount_cast_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:00:27.406298+00:00
-- url     : https://prove2.me/theorems/677b97a4-3ca6-4fcc-a5dd-652cd13f8951
-- title:
--   FD1 D: leaf Count cast pos
-- statement:
--   The FD1 D construction uses the leaf Count cast pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Parameters.lean#L118-L120
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Parameters.lean#L118-L120

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Parameters
set_option autoImplicit true
open FD1D
noncomputable section
open Filter Asymptotics

theorem FD1D.leafCount_cast_pos (m : ℕ) :
    0 < (leafCount m : ℝ) := by sorry
