-- Prove2me | Theorems.Thm_FD1D_initialization_average_bound
-- name    : FD1D.initialization_average_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:05:24.994796+00:00
-- url     : https://prove2.me/theorems/b25d44ca-0927-5b87-bb9b-23a41978e374
-- title:
--   FD1 D: initialization average bound
-- statement:
--   Adding at most `m` initialization cost preserves the advertised constant.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Drift.lean#L156-L171
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Drift.lean#L156-L171

import Definitions.Def_FD1D_Arithmetic
import Definitions.Def_FD1D_Drift
set_option autoImplicit true
open FD1D
noncomputable section

theorem FD1D.initialization_average_bound
    {a m N mainCost : ℝ}
    (ha : 1 ≤ a) (hm : 0 < m) (hN : m ^ 2 ≤ N)
    (hmain : mainCost ≤ 6 * a / m) :
    m / N + mainCost ≤ 7 * a / m := by sorry
