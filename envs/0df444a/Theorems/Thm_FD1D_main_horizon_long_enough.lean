-- Prove2me | Theorems.Thm_FD1D_main_horizon_long_enough
-- name    : FD1D.main_horizon_long_enough
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:05:41.023347+00:00
-- url     : https://prove2.me/theorems/244d6703-5dcb-4aab-9569-6dc7aa07035f
-- title:
--   FD1 D: main horizon long enough
-- statement:
--   The initialization-period arithmetic used in the final horizon bound.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Drift.lean#L149-L153
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Drift.lean#L149-L153

import Definitions.Def_FD1D_Arithmetic
import Definitions.Def_FD1D_Drift
set_option autoImplicit true
open FD1D
noncomputable section

theorem FD1D.main_horizon_long_enough {m N : ℕ} (hm : 1 ≤ m)
    (hN : 2 * m ^ 2 ≤ N) : m ^ 2 ≤ N - m := by sorry
