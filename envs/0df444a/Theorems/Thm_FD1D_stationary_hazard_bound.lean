-- Prove2me | Theorems.Thm_FD1D_stationary_hazard_bound
-- name    : FD1D.stationary_hazard_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:04:36.060164+00:00
-- url     : https://prove2.me/theorems/ce25eb13-87f4-42b2-8756-dffd0b324770
-- title:
--   FD1 D: stationary hazard bound
-- statement:
--   The numerical core of the stationary hazard estimate.  This is equation (11)
--   after the deterministic Bellman lower bound and the stochastic remainder
--   upper bound have been combined.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Drift.lean#L89-L110
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Drift.lean#L89-L110

import Definitions.Def_FD1D_Arithmetic
import Definitions.Def_FD1D_Drift
set_option autoImplicit true
open FD1D
noncomputable section

theorem FD1D.stationary_hazard_bound
    {a L m H : ℝ}
    (ha : 0 < a) (hm : 0 < m) (hL : 0 ≤ L) (hH : 0 ≤ H)
    (haL : 200 * L ≤ a)
    (hmain :
      (a / 100 - L) * H ≤ 103 * a / (300 * m ^ 2)) :
    H ≤ 206 / (3 * m ^ 2) := by sorry
