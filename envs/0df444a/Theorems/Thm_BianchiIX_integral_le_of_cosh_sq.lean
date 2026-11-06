-- Prove2me | Theorems.Thm_BianchiIX_integral_le_of_cosh_sq
-- name    : BianchiIX.integral_le_of_cosh_sq
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-05T00:36:10.124202+00:00
-- url     : https://prove2.me/theorems/983a2a0b-2ed4-4889-a3cf-f6ea6a7ad3b2
-- title:
--   Integrating a squared-cosh envelope from endpoint bounds
-- statement:
--   Let $a\leq b$, $B\geq0$, and let $f$ be continuous
--   on $[a,b]$. Suppose $f(z)\leq B\cosh^2z$ on this interval and
--   $\cosh a,\cosh b\leq K$. Then
--   $$\int_a^b f(z)\,dz\leq2BK^2.$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Analysis/CoreIntegrals.lean#L72-L84

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

theorem BianchiIX.integral_le_of_cosh_sq {f : ℝ → ℝ} {a b B K : ℝ} (hab : a ≤ b)
    (hB : 0 ≤ B) (hf : ContinuousOn f (Icc a b))
    (hbound : ∀ z ∈ Icc a b, f z ≤ B * Real.cosh z ^ 2)
    (ha : Real.cosh a ≤ K) (hb : Real.cosh b ≤ K) :
    (∫ z in a..b, f z) ≤ 2 * B * K ^ 2 := by sorry
