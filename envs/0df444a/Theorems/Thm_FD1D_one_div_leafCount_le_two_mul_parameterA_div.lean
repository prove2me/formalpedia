-- Prove2me | Theorems.Thm_FD1D_one_div_leafCount_le_two_mul_parameterA_div
-- name    : FD1D.one_div_leafCount_le_two_mul_parameterA_div
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:17:33.762121+00:00
-- url     : https://prove2.me/theorems/eb84a143-2e0b-55e2-8a23-9947293a96b4
-- title:
--   FD1 D: one div leaf Count le two mul parameter A div
-- statement:
--   The paper's estimate `1/n ≤ 2a/m`, over the reals.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Parameters.lean#L166-L172
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Parameters.lean#L166-L172

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Parameters
set_option autoImplicit true
open FD1D
noncomputable section
open Filter Asymptotics

theorem FD1D.one_div_leafCount_le_two_mul_parameterA_div {m : ℕ}
    (hm : 1 ≤ m) :
    (1 : ℝ) / leafCount m ≤ 2 * parameterA m / m := by sorry
