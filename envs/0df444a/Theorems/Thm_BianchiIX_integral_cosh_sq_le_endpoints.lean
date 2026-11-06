-- Prove2me | Theorems.Thm_BianchiIX_integral_cosh_sq_le_endpoints
-- name    : BianchiIX.integral_cosh_sq_le_endpoints
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-05T00:33:09.461491+00:00
-- url     : https://prove2.me/theorems/65d00d4a-3285-447a-b598-0806715c2e62
-- title:
--   Endpoint control of the squared hyperbolic cosine integral
-- statement:
--   For $a\leq b$,
--   $$\int_a^b\cosh^2 z\,dz\leq\cosh^2 a+\cosh^2 b.$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Analysis/CoreIntegrals.lean#L54-L70

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

theorem BianchiIX.integral_cosh_sq_le_endpoints {a b : ℝ} (hab : a ≤ b) :
    (∫ z in a..b, Real.cosh z ^ 2) ≤ Real.cosh a ^ 2 + Real.cosh b ^ 2 := by sorry
