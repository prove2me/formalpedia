-- Prove2me | Theorems.Thm_BianchiIX_partial_core_radial_derivative_budget
-- name    : BianchiIX.partial_core_radial_derivative_budget
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-05T06:48:28.941916+00:00
-- url     : https://prove2.me/theorems/58762681-bd9a-46fb-a7fe-c7a48b22ac4c
-- title:
--   Moving entrance derivatives retain the weak radial amplitude
-- statement:
--   Suppose $0<r\leq1$, $K\geq1$, $k>0$,
--   $1/k\leq Kr$, $k\leq K/r$, $U\geq0$, and $0\leq P\leq1$. Assume
--   $$|dR|\leq K/r^2,\quad |dU|\leq KU/r,\quad
--   |dP|\leq KP/r,\quad |dz|\leq K/r.$$
--   Then
--   $$|dU|+\frac{(U+P)(|dR|+|dP|)}k
--   +(kU+P^2/k)|dz|\leq\frac{4K^2(U+rP)}{r^2}.$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Algebra/PartialCoreRadialResponseBounds.lean#L8-L72

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

theorem BianchiIX.partial_core_radial_derivative_budget {r K k U P dR dU dP dz : ℝ}
    (hr : 0 < r ∧ r ≤ 1) (hK : 1 ≤ K) (hk : 0 < k)
    (hki : 1 / k ≤ K * r) (hkhi : k ≤ K / r)
    (hU : 0 ≤ U) (hP : 0 ≤ P ∧ P ≤ 1)
    (hR : |dR| ≤ K / r ^ 2) (hdU : |dU| ≤ K * U / r)
    (hdP : |dP| ≤ K * P / r) (hdz : |dz| ≤ K / r) :
    |dU| + (U + P) * (|dR| + |dP|) / k + (k * U + P ^ 2 / k) * |dz| ≤
      4 * K ^ 2 * (U + r * P) / r ^ 2 := by sorry
