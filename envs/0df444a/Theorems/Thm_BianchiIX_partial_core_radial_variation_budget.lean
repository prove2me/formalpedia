-- Prove2me | Theorems.Thm_BianchiIX_partial_core_radial_variation_budget
-- name    : BianchiIX.partial_core_radial_variation_budget
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-05T06:54:24.344686+00:00
-- url     : https://prove2.me/theorems/5cb81698-9d93-49cc-ac10-8d69b760fbc6
-- title:
--   The complete radial variation has a uniform inverse square bound
-- statement:
--   Suppose $0<r\leq1$, $K\geq1$, $k>0$,
--   $1/k\leq Kr$, $k\leq K/r$, $U\geq0$, $kU\leq1$, and $0\leq P\leq1$.
--   Assume
--   $$|dR|\leq K/r^2,\quad |dU|\leq KU/r,\quad
--   |dP|\leq KP/r,\quad |dz|\leq K/r.$$
--   Then
--   $$|dR|+k|dU|+|dP|+(k^2U+P/k)|dz|\leq5K^2/r^2.$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Algebra/PartialCoreRadialMultiplierBounds.lean#L7-L49

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

theorem BianchiIX.partial_core_radial_variation_budget {r K k U P dR dU dP dz : ℝ}
    (hr : 0 < r ∧ r ≤ 1) (hK : 1 ≤ K) (hk : 0 < k)
    (hki : 1 / k ≤ K * r) (hkhi : k ≤ K / r)
    (_hU : 0 ≤ U) (hKU : k * U ≤ 1) (hP : 0 ≤ P ∧ P ≤ 1)
    (hR : |dR| ≤ K / r ^ 2) (hdU : |dU| ≤ K * U / r)
    (hdP : |dP| ≤ K * P / r) (hdz : |dz| ≤ K / r) :
    |dR| + k * |dU| + |dP| + (k ^ 2 * U + P / k) * |dz| ≤ 5 * K ^ 2 / r ^ 2 := by sorry
