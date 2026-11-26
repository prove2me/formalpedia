-- Prove2me | Theorems.Thm_FD1D_leafCount_cast_ne_zero
-- name    : FD1D.leafCount_cast_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:17:06.874042+00:00
-- url     : https://prove2.me/theorems/f076d03f-dbaa-5642-820d-7cf2ef669209
-- title:
--   FD1 D: leaf Count cast ne zero
-- statement:
--   The FD1 D construction uses the leaf Count cast ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Parameters.lean#L122-L124
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Parameters.lean#L122-L124

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Parameters
set_option autoImplicit true
open FD1D
noncomputable section
open Filter Asymptotics

theorem FD1D.leafCount_cast_ne_zero (m : ℕ) :
    (leafCount m : ℝ) ≠ 0 := by sorry
