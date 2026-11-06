-- Prove2me | Theorems.Thm_BianchiIX_core_four_integral_bounds
-- name    : BianchiIX.core_four_integral_bounds
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-05T00:37:39.653013+00:00
-- url     : https://prove2.me/theorems/52bd6bf9-4aa1-4e6f-8459-4a9215c246fe
-- title:
--   Four integral estimates for radial core drift
-- statement:
--   Let $a\leq b$, $k\geq6$, and $u_0,w_0\geq0$.
--   Let $r,u,v,w$ be continuous on $[a,b]$. Assume there
--   $$r(z)\geq9k/10,\qquad0\leq u(z)\leq u_0e^{-k(z-a)/4},$$
--   $$0\leq v(z)\leq(11/10)e^{z-a},\qquad
--   0\leq w(z)\leq w_0,\qquad w(z)\leq w_0\cosh z/r(z),$$
--   and $\cosh a,\cosh b\leq11k/10$. Then
--   $$\int_a^b uv\leq\frac{14u_0}{k},\qquad
--   \int_a^b uw\leq\frac{4u_0w_0}{k},$$
--   $$\int_a^b\frac{u^2}r\leq\frac{3u_0^2}{k^2},\qquad
--   \int_a^b\frac{w^2}r\leq\frac{4w_0^2}{k}.$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Analysis/CoreRadialIntegral.lean#L10-L80

import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.Tactic.GCongr

namespace BianchiIX
end BianchiIX

noncomputable section
open BianchiIX
open Set MeasureTheory

theorem BianchiIX.core_four_integral_bounds {r u v w : ℝ → ℝ} {a b k u₀ w₀ : ℝ}
    (hab : a ≤ b) (hk : 6 ≤ k) (hu₀ : 0 ≤ u₀) (hw₀ : 0 ≤ w₀)
    (hrc : ContinuousOn r (Icc a b)) (huc : ContinuousOn u (Icc a b))
    (hvc : ContinuousOn v (Icc a b)) (hwc : ContinuousOn w (Icc a b))
    (hr : ∀ z ∈ Icc a b, 9 / 10 * k ≤ r z)
    (hu : ∀ z ∈ Icc a b, 0 ≤ u z ∧ u z ≤ u₀ * Real.exp (-k * (z - a) / 4))
    (hv : ∀ z ∈ Icc a b, 0 ≤ v z ∧ v z ≤ (11 / 10) * Real.exp (z - a))
    (hw : ∀ z ∈ Icc a b, 0 ≤ w z ∧ w z ≤ w₀ ∧ w z ≤ w₀ * Real.cosh z / r z)
    (ha : Real.cosh a ≤ 11 / 10 * k) (hb : Real.cosh b ≤ 11 / 10 * k) :
    (∫ z in a..b, u z * v z) ≤ 14 * u₀ / k ∧
    (∫ z in a..b, u z * w z) ≤ 4 * u₀ * w₀ / k ∧
    (∫ z in a..b, u z ^ 2 / r z) ≤ 3 * u₀ ^ 2 / k ^ 2 ∧
    (∫ z in a..b, w z ^ 2 / r z) ≤ 4 * w₀ ^ 2 / k := by sorry
