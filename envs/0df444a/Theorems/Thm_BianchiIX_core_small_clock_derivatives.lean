-- Prove2me | Theorems.Thm_BianchiIX_core_small_clock_derivatives
-- name    : BianchiIX.core_small_clock_derivatives
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-04T23:58:27.714534+00:00
-- url     : https://prove2.me/theorems/e72604e3-51d4-4159-944a-e799c14eef0c
-- title:
--   Bounds for the derivatives of the core clock factor
-- statement:
--   Suppose $r\geq5$, $0\leq\varepsilon\leq1/100$,
--   $0\leq u,w\leq\varepsilon$, and $v>0$. Then
--   $$\left|\frac{2(u-w)(u-2w)}{r^3}\right|\leq\frac\varepsilon{r^2},
--   \qquad \left|\frac{-2(u-w)}{r^2}\right|\leq\frac{2\varepsilon}{r^2},$$
--   $$\left|\frac{2(u-w)}{vr^2}\right|\leq\frac{2\varepsilon}{vr^2}.$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Algebra/CoreCoefficientEstimates.lean#L93-L118

import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp

namespace BianchiIX
end BianchiIX

noncomputable section
open BianchiIX

theorem BianchiIX.core_small_clock_derivatives {r m u w v : ℝ} (hr : 5 ≤ r)
    (hm : 0 ≤ m ∧ m ≤ 1 / 100) (hu : 0 ≤ u ∧ u ≤ m) (hw : 0 ≤ w ∧ w ≤ m)
    (hv : 0 < v) :
    |2 * (u - w) * (u - 2 * w) / r ^ 3| ≤ m / r ^ 2 ∧
    |-2 * (u - w) / r ^ 2| ≤ 2 * m / r ^ 2 ∧
    |2 * (u - w) / (v * r ^ 2)| ≤ 2 * m / (v * r ^ 2) := by sorry
