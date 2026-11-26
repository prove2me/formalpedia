-- Prove2me | Theorems.Thm_FD1D_natFloor_parameterRatio
-- name    : FD1D.natFloor_parameterRatio
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:59:43.665912+00:00
-- url     : https://prove2.me/theorems/0b1855be-68c8-4c6f-b5e1-269e498959c3
-- title:
--   FD1 D: nat Floor parameter Ratio
-- statement:
--   The FD1 D construction uses the nat Floor parameter Ratio property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Parameters.lean#L61-L64
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Parameters.lean#L61-L64

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Parameters
set_option autoImplicit true
open FD1D
noncomputable section
open Filter Asymptotics

theorem FD1D.natFloor_parameterRatio (m : ℕ) :
    ⌊(m : ℝ) / (parameterA m : ℝ)⌋₊ = m / parameterA m := by sorry
