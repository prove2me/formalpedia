-- Prove2me | Theorems.Thm_BianchiIX_integral_clock_exp_decay
-- name    : BianchiIX.integral_clock_exp_decay
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-05T07:44:40.517338+00:00
-- url     : https://prove2.me/theorems/6f73d90c-5be4-45c9-8879-2a4f0cb4b9bd
-- title:
--   An exponential clock weight has an exact integral
-- statement:
--   Let $a\leq b$ and $c>0$. Suppose $z$ has derivative $q(t)$
--   at every $t\in[a,b]$ and $q$ is continuous there. Then
--   $$\int_a^b q(t)e^{-c(z(t)-z(a))}\,dt
--   =\frac{1-e^{-c(z(b)-z(a))}}c.$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Analysis/ClockDecayIntegrals.lean#L10-L26

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
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Data.Matrix.Mul

namespace BianchiIX
end BianchiIX

noncomputable section
open BianchiIX
open Set MeasureTheory

theorem BianchiIX.integral_clock_exp_decay {z z' : ℝ → ℝ} {a b c : ℝ}
    (hab : a ≤ b) (hc : 0 < c)
    (hz : ∀ t ∈ Icc a b, HasDerivAt z (z' t) t)
    (hzc : ContinuousOn z' (Icc a b)) :
    (∫ t in a..b, z' t * Real.exp (-c * (z t - z a))) =
      (1 - Real.exp (-c * (z b - z a))) / c := by sorry
