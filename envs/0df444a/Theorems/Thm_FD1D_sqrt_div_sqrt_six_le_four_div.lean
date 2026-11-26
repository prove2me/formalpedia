-- Prove2me | Theorems.Thm_FD1D_sqrt_div_sqrt_six_le_four_div
-- name    : FD1D.sqrt_div_sqrt_six_le_four_div
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:33:10.978005+00:00
-- url     : https://prove2.me/theorems/d6c305e7-fc22-4cb8-888b-f07df1885269
-- title:
--   FD1 D: sqrt div sqrt six le four div
-- statement:
--   The FD1 D construction uses the sqrt div sqrt six le four div property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Arithmetic.lean#L13-L27
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Arithmetic.lean#L13-L27

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Arithmetic
set_option autoImplicit true
open FD1D
noncomputable section

theorem FD1D.sqrt_div_sqrt_six_le_four_div
    {x m : ℝ} (hm : 0 < m) (hx0 : 0 ≤ x)
    (hx : x ≤ 96 / m ^ 2) :
    Real.sqrt x / Real.sqrt 6 ≤ 4 / m := by sorry
