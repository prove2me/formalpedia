-- Prove2me | Theorems.Thm_BianchiIX_core_small_radius_derivatives
-- name    : BianchiIX.core_small_radius_derivatives
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-05T00:04:03.912168+00:00
-- url     : https://prove2.me/theorems/b8f4a110-c453-4d6a-ada4-94f26f31c332
-- title:
--   Bounds for the derivatives of the radial numerator
-- statement:
--   Suppose $r\geq5$, $0\leq\varepsilon\leq1/100$,
--   $0\leq u,w\leq\varepsilon$, $1\leq v\leq r$, $0\leq s\leq1$,
--   and $|c|\leq1$. Then
--   $$\left|-u(s-w/r)+\frac{c(u-w)(3w-u)}{r^2}\right|\leq2\varepsilon,$$
--   $$\left|-(v-2u+w)+\frac{2c(u-w)}r+v\right|\leq3\varepsilon,$$
--   $$\left|-\frac uv-\frac{2c(u-w)}{rv}\right|\leq\frac{2\varepsilon}v.$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Algebra/CoreCoefficientEstimates.lean#L166-L210

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

theorem BianchiIX.core_small_radius_derivatives {r m u v w s c : ℝ} (hr : 5 ≤ r)
    (hm : 0 ≤ m ∧ m ≤ 1 / 100) (hu : 0 ≤ u ∧ u ≤ m) (hw : 0 ≤ w ∧ w ≤ m)
    (hv : 1 ≤ v ∧ v ≤ r) (hs : 0 ≤ s ∧ s ≤ 1) (hc : |c| ≤ 1) :
    |-u * (s - w / r) + c * (u - w) * (3 * w - u) / r ^ 2| ≤ 2 * m ∧
    |(-(v - 2 * u + w) + 2 * c * (u - w) / r) + v| ≤ 3 * m ∧
    |-u / v - 2 * c * (u - w) / (r * v)| ≤ 2 * m / v := by sorry
