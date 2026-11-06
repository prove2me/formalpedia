-- Prove2me | Theorems.Thm_BianchiIX_coreBootstrap_coefficient_scales
-- name    : BianchiIX.coreBootstrap_coefficient_scales
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-04T23:58:26.467697+00:00
-- url     : https://prove2.me/theorems/92c07738-6ae2-498d-9816-75856404d3eb
-- title:
--   Uniform numerical scales for the core coefficient estimates
-- statement:
--   Let $k\geq6$, $99k/100\leq r\leq101k/100$, and
--   $\varepsilon=1/(10000k)$. Then
--   $$r\geq5,\quad 0\leq\varepsilon\leq\frac1{100},\quad
--   r\varepsilon\leq\frac1{1000},\quad
--   \frac\varepsilon r\leq\frac1{100},$$
--   $$\frac kr\leq\frac32,\quad \frac{k^2}{r^2}\leq\frac32,\quad
--   \frac{4\varepsilon^2}{r}\leq\frac\varepsilon{10}.$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Algebra/CoreCoefficientEstimates.lean#L7-L32

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

theorem BianchiIX.coreBootstrap_coefficient_scales {k r : ℝ} (hk : 6 ≤ k)
    (hr : 99 / 100 * k ≤ r ∧ r ≤ 101 / 100 * k) :
    let m := (1 / 10000) / k
    5 ≤ r ∧ 0 ≤ m ∧ m ≤ 1 / 100 ∧ r * m ≤ 1 / 1000 ∧
    m / r ≤ 1 / 100 ∧ k / r ≤ 3 / 2 ∧ k ^ 2 / r ^ 2 ≤ 3 / 2 ∧
    4 * m ^ 2 / r ≤ m / 10 := by sorry
