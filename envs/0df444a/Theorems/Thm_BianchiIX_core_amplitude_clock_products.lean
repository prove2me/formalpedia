-- Prove2me | Theorems.Thm_BianchiIX_core_amplitude_clock_products
-- name    : BianchiIX.core_amplitude_clock_products
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-05T02:29:08.050426+00:00
-- url     : https://prove2.me/theorems/08205e42-a4bd-4fba-827e-6a61acfe34a2
-- title:
--   Clock-derivative products with explicit wall amplitudes
-- statement:
--   Assume $r\geq5$, $0\leq\mu\leq1/100$,
--   $0\leq u,w\leq\mu$, and $|g|\leq2r\mu$. Then
--   $$\left|g\frac{2(u-w)(u-2w)}{r^3}\right|
--   \leq\frac{u+w^2/r^2}{10},$$
--   $$\left|g\frac{-2(u-w)}{r^2}\right|
--   \leq\frac{u+w/r}{10}.$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Algebra/CoreAmplitudeCoefficients.lean#L30-L73

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

theorem BianchiIX.core_amplitude_clock_products {r m u w g : ℝ} (hr : 5 ≤ r)
    (hm : 0 ≤ m ∧ m ≤ 1 / 100) (hu : 0 ≤ u ∧ u ≤ m) (hw : 0 ≤ w ∧ w ≤ m)
    (hg : |g| ≤ 2 * r * m) :
    |g * (2 * (u - w) * (u - 2 * w) / r ^ 3)| ≤ (u + w ^ 2 / r ^ 2) / 10 ∧
    |g * (-2 * (u - w) / r ^ 2)| ≤ (u + w / r) / 10 := by sorry
