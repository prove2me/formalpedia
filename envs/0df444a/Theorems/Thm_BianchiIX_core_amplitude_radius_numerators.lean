-- Prove2me | Theorems.Thm_BianchiIX_core_amplitude_radius_numerators
-- name    : BianchiIX.core_amplitude_radius_numerators
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-05T02:29:27.019786+00:00
-- url     : https://prove2.me/theorems/d8c834f1-835b-42d2-b53e-c29787fd9400
-- title:
--   The radial-row numerators preserve the weak-wall power and radius scale
-- statement:
--   Assume $r\geq5$, $0\leq\mu\leq1/100$,
--   $0\leq u,w\leq\mu$, $1\leq v\leq r$, $0\leq s\leq1$,
--   and $|c|\leq1$. Set $d=1-(u-w)^2/r^2$. Then
--   $$\left|-u(s-w/r)+c(u-w)(3w-u)/r^2\right|
--   \leq2u+3w^2/r^2,$$
--   $$\left|-(v-2u+w)+2c(u-w)/r+v-v(1-d)\right|\leq4(u+w),$$
--   $$\left|v\left(-u/v-2c(u-w)/(rv)\right)\right|\leq2(u+w/r).$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Algebra/CoreAmplitudeCoefficients.lean#L75-L149

import Definitions.Def_BianchiIX_Algebra_CoreAngle
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp

noncomputable section
open BianchiIX

theorem BianchiIX.core_amplitude_radius_numerators {r m u v w s c : ℝ} (hr : 5 ≤ r)
    (hm : 0 ≤ m ∧ m ≤ 1 / 100) (hu : 0 ≤ u ∧ u ≤ m) (hw : 0 ≤ w ∧ w ≤ m)
    (hv : 1 ≤ v ∧ v ≤ r) (hs : 0 ≤ s ∧ s ≤ 1) (hc : |c| ≤ 1) :
    |-u * (s - w / r) + c * (u - w) * (3 * w - u) / r ^ 2| ≤ 2 * u + 3 * w ^ 2 / r ^ 2 ∧
    |(-(v - 2 * u + w) + 2 * c * (u - w) / r) + v - v * (1 - coreClockFactor r u w)| ≤
      4 * (u + w) ∧
    |v * (-u / v - 2 * c * (u - w) / (r * v))| ≤ 2 * (u + w / r) := by sorry
