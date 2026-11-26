-- Prove2me | Theorems.Thm_FD1D_V5_parameterA_cast_le_log
-- name    : FD1D.V5.parameterA_cast_le_log
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:12:19.49947+00:00
-- url     : https://prove2.me/theorems/5e415ef6-fb95-4dee-a162-808c64855d65
-- title:
--   V5: parameter A cast le log
-- statement:
--   Explicit natural-log form of `a = O(log m)`, valid for `m ≥ 2`.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/V5/Parameters.lean#L199-L207
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/V5/Parameters.lean#L199-L207

import Definitions.Def_FD1D_Tree
import Definitions.Def_FD1D_V5_Parameters
set_option autoImplicit true
open FD1D FD1D.V5
noncomputable section
open Filter Asymptotics

theorem FD1D.V5.parameterA_cast_le_log {m : ℕ} (hm : 2 ≤ m) :
    (parameterA m : ℝ) ≤
      (8000 / Real.log 2) * Real.log (m : ℝ) := by sorry
