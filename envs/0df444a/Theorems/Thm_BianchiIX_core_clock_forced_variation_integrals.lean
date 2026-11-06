-- Prove2me | Theorems.Thm_BianchiIX_core_clock_forced_variation_integrals
-- name    : BianchiIX.core_clock_forced_variation_integrals
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-05T01:59:49.592493+00:00
-- url     : https://prove2.me/theorems/084d1fbd-d380-436d-9b15-3d3c44702581
-- title:
--   The two forced-variation integrals in the original time variable
-- statement:
--   Let $k\geq6$, $a\leq b$, and $U,Q\geq0$.
--   Suppose $x$ and $\omega$ are continuous on $[a,b]$,
--   $z'(t)=\omega(t)\geq0$ throughout this interval,
--   $\cosh z(a)=k$, and
--   $$|x(t)|\leq e^{-k(z(t)-z(a))/4}
--   \bigl(|x(a)|+3kUQ(z(t)-z(a))\bigr).$$
--   Then
--   $$\int_a^b\frac{|x(t)|}{\cosh z(t)}\omega(t)\,dt
--   \leq\frac{12|x(a)|+432UQ}{k^2},$$
--   $$\int_a^b|x(t)|\omega(t)\,dt
--   \leq\frac{4|x(a)|+48UQ}{k}.$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Analysis/ClockEnvelope.lean#L27-L85

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
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

namespace BianchiIX
end BianchiIX

noncomputable section
open BianchiIX
open Set MeasureTheory

theorem BianchiIX.core_clock_forced_variation_integrals {x z rate : ℝ → ℝ} {k a b U Q : ℝ}
    (hk : 6 ≤ k) (hab : a ≤ b) (hU : 0 ≤ U) (hQ : 0 ≤ Q)
    (hx : ContinuousOn x (Icc a b)) (hz : ∀ t ∈ Icc a b, HasDerivAt z (rate t) t)
    (hrate : ContinuousOn rate (Icc a b)) (hpos : ∀ t ∈ Icc a b, 0 ≤ rate t)
    (hentry : Real.cosh (z a) = k)
    (hbound : ∀ t ∈ Icc a b, |x t| ≤ Real.exp (-k * (z t - z a) / 4) *
      (|x a| + 3 * k * U * Q * (z t - z a))) :
    (∫ t in a..b, (|x t| / Real.cosh (z t)) * rate t) ≤ (12 * |x a| + 432 * U * Q) / k ^ 2 ∧
      (∫ t in a..b, |x t| * rate t) ≤ (4 * |x a| + 48 * U * Q) / k := by sorry
