-- Prove2me | Theorems.Thm_FD1D_parameterA_cast_le_log
-- name    : FD1D.parameterA_cast_le_log
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:01:15.472974+00:00
-- url     : https://prove2.me/theorems/d49eed13-7d23-5088-a5a0-cae2d190b1f6
-- title:
--   FD1 D: parameter A cast le log
-- statement:
--   Explicit natural-log form of `a = O(log m)`, valid for `m ≥ 2`.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Parameters.lean#L209-L217
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Parameters.lean#L209-L217

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Parameters
set_option autoImplicit true
open FD1D
noncomputable section
open Filter Asymptotics

theorem FD1D.parameterA_cast_le_log {m : ℕ} (hm : 2 ≤ m) :
    (parameterA m : ℝ) ≤
      (800 / Real.log 2) * Real.log m := by sorry
