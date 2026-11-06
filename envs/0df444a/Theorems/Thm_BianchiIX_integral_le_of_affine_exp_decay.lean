-- Prove2me | Theorems.Thm_BianchiIX_integral_le_of_affine_exp_decay
-- name    : BianchiIX.integral_le_of_affine_exp_decay
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-05T01:56:13.196399+00:00
-- url     : https://prove2.me/theorems/f57ed66f-e4d1-4ce1-a9ad-09c53aeac473
-- title:
--   Integrating an affine factor times exponential decay
-- statement:
--   Suppose $a\leq b$, $c>0$, and $A,B\geq0$.
--   If $f$ is continuous on $[a,b]$ and
--   $$f(t)\leq e^{-c(t-a)}(A+B(t-a))\qquad(t\in[a,b]),$$
--   then
--   $$\int_a^b f(t)\,dt\leq A/c+B/c^2.$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Analysis/ForcedDecayIntegrals.lean#L25-L42

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

namespace BianchiIX
end BianchiIX

noncomputable section
open BianchiIX
open Set MeasureTheory

theorem BianchiIX.integral_le_of_affine_exp_decay {f : ℝ → ℝ} {a b c A B : ℝ}
    (hab : a ≤ b) (hc : 0 < c) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hf : ContinuousOn f (Icc a b))
    (hbound : ∀ t ∈ Icc a b, f t ≤ Real.exp (-c * (t - a)) * (A + B * (t - a))) :
    (∫ t in a..b, f t) ≤ A / c + B / c ^ 2 := by sorry
