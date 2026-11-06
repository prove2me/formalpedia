-- Prove2me | Theorems.Thm_BianchiIX_core_log_weak_products
-- name    : BianchiIX.core_log_weak_products
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-05T02:26:42.722196+00:00
-- url     : https://prove2.me/theorems/f8b704d5-69ad-48a8-8326-dd842162ec3a
-- title:
--   Three denominator corrections in the weak logarithmic rate
-- statement:
--   Suppose $r\geq5$, $v\geq1$, and
--   $0\leq\mu,c\leq1/100$. Then
--   $$\frac{2(1+c)}r\frac\mu{r^2}\leq\frac1{r^2},\qquad
--   \frac{2(1+c)}r\frac{2\mu}{r^2}\leq1,\qquad
--   \frac{2(1+c)}r\frac{2\mu}{vr^2}\leq\frac\mu r.$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Algebra/CoreLogRateEstimates.lean#L21-L45

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

theorem BianchiIX.core_log_weak_products {r m v c : ℝ} (hr : 5 ≤ r)
    (hm : 0 ≤ m ∧ m ≤ 1 / 100) (hv : 1 ≤ v) (hc : 0 ≤ c ∧ c ≤ 1 / 100) :
    (2 * (1 + c) / r) * (m / r ^ 2) ≤ 1 / r ^ 2 ∧
      (2 * (1 + c) / r) * (2 * m / r ^ 2) ≤ 1 ∧
      (2 * (1 + c) / r) * (2 * m / (v * r ^ 2)) ≤ m / r := by sorry
