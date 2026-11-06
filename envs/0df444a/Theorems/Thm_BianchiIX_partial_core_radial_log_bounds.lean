-- Prove2me | Theorems.Thm_BianchiIX_partial_core_radial_log_bounds
-- name    : BianchiIX.partial_core_radial_log_bounds
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-05T06:59:11.826678+00:00
-- url     : https://prove2.me/theorems/85a06b8a-1806-48dd-948e-57803a00adcc
-- title:
--   Radial logarithmic variations separate the strong and weak scales
-- statement:
--   Let $r,k>0$, $K,L\geq1$, $B\geq0$,
--   $1/k\leq Kr$, $k\leq K/r$, $Q\leq5K^2/r^2$, and $|dz|\leq K/r$.
--   If
--   $$|\ell_U|\leq40BLQ+2k|dz|,\qquad
--   |\ell_P|\leq236BLQ/k^2+4|dz|/k,$$
--   then
--   $$|\ell_U|\leq(200B+2)K^2L/r^2,\qquad
--   |\ell_P|\leq(1180BK^4+4K^2)L.$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Algebra/PartialCoreRadialMultiplierBounds.lean#L51-L83

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr

namespace BianchiIX
end BianchiIX

noncomputable section
open BianchiIX

theorem BianchiIX.partial_core_radial_log_bounds {r K k B L Q dz lU lP : ℝ}
    (hr : 0 < r) (hK : 1 ≤ K) (hk : 0 < k) (hB : 0 ≤ B) (hL : 1 ≤ L)
    (hki : 1 / k ≤ K * r) (hkhi : k ≤ K / r)
    (hQ : Q ≤ 5 * K ^ 2 / r ^ 2) (hdz : |dz| ≤ K / r)
    (hU : |lU| ≤ 40 * B * L * Q + 2 * k * |dz|)
    (hP : |lP| ≤ 236 * B * L * Q / k ^ 2 + 4 * |dz| / k) :
    |lU| ≤ (200 * B + 2) * K ^ 2 * L / r ^ 2 ∧
      |lP| ≤ (1180 * B * K ^ 4 + 4 * K ^ 2) * L := by sorry
