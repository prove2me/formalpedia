-- Prove2me | Theorems.Thm_BianchiIX_core_small_strong_derivatives
-- name    : BianchiIX.core_small_strong_derivatives
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-04T23:59:40.039623+00:00
-- url     : https://prove2.me/theorems/0be44ba7-79e3-44de-b902-485c48ded4cc
-- title:
--   Bounds for the radius and product derivatives of the strong numerator
-- statement:
--   Suppose $r\geq5$, $0\leq\varepsilon\leq1/100$,
--   $0\leq u,w\leq\varepsilon$, $v\geq1$, and $0\leq s\leq1$. Then
--   $$\left|-\frac12-\frac{sw}{r}
--   +\frac{3w^2-u^2}{2r^2}\right|\leq\frac34,
--   \qquad \left|\frac{1-w/v}{r}\right|\leq\frac1r.$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Algebra/CoreCoefficientEstimates.lean#L134-L164

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

theorem BianchiIX.core_small_strong_derivatives {r m u v w s : ℝ} (hr : 5 ≤ r)
    (hm : 0 ≤ m ∧ m ≤ 1 / 100) (hu : 0 ≤ u ∧ u ≤ m) (hw : 0 ≤ w ∧ w ≤ m)
    (hv : 1 ≤ v) (hs : 0 ≤ s ∧ s ≤ 1) :
    |-1 / 2 - s * w / r + (3 * w ^ 2 - u ^ 2) / (2 * r ^ 2)| ≤ 3 / 4 ∧
    |(1 - w / v) / r| ≤ 1 / r := by sorry
