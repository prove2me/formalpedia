-- Prove2me | Theorems.Thm_FD1D_stationary_sqrt_term_le
-- name    : FD1D.stationary_sqrt_term_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:33:09.379536+00:00
-- url     : https://prove2.me/theorems/b399297f-11c8-5d3c-bded-67bfc6435f8a
-- title:
--   FD1 D: stationary sqrt term le
-- statement:
--   The FD1 D construction uses the stationary sqrt term le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Arithmetic.lean#L29-L40
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Arithmetic.lean#L29-L40

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Arithmetic
set_option autoImplicit true
open FD1D
noncomputable section

theorem FD1D.stationary_sqrt_term_le
    {H m : ℝ} (hm : 0 < m)
    (hH0 : 1 / m ^ 2 ≤ H)
    (hH : H ≤ 206 / (3 * m ^ 2)) :
    Real.sqrt (H - 1 / m ^ 2) / Real.sqrt 6 ≤ 4 / m := by sorry
