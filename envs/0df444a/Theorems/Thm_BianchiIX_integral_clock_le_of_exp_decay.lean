-- Prove2me | Theorems.Thm_BianchiIX_integral_clock_le_of_exp_decay
-- name    : BianchiIX.integral_clock_le_of_exp_decay
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-05T02:28:48.798347+00:00
-- url     : https://prove2.me/theorems/b2accb30-aa13-43a1-8746-708a5aaaa41e
-- title:
--   Integrating exponential decay against its nondecreasing clock
-- statement:
--   Let $a\leq b$, $c>0$, $B\geq0$, and let
--   $f,\omega$ be continuous on $[a,b]$. Suppose there that
--   $z'(t)=\omega(t)\geq0$ and $f(t)\leq B e^{-c(z(t)-z(a))}$.
--   Then
--   $$\int_a^b f(t)\omega(t)\,dt\leq B/c.$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Analysis/ClockWeightIntegrals.lean#L25-L34

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

theorem BianchiIX.integral_clock_le_of_exp_decay {f z rate : ℝ → ℝ} {a b c B : ℝ}
    (hab : a ≤ b) (hz : ∀ t ∈ Icc a b, HasDerivAt z (rate t) t)
    (hrate : ContinuousOn rate (Icc a b)) (hpos : ∀ t ∈ Icc a b, 0 ≤ rate t)
    (hc : 0 < c) (hB : 0 ≤ B) (hf : ContinuousOn f (Icc a b))
    (hbound : ∀ t ∈ Icc a b, f t ≤ B * Real.exp (-c * (z t - z a))) :
    (∫ t in a..b, f t * rate t) ≤ B / c := by sorry
