-- Prove2me | Theorems.Thm_BianchiIX_abs_sub_le_integral_bound
-- name    : BianchiIX.abs_sub_le_integral_bound
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-05T00:33:24.160867+00:00
-- url     : https://prove2.me/theorems/7eba07d6-fbb7-428c-9f26-e1e8428b6450
-- title:
--   Bounding displacement by a continuous derivative envelope
-- statement:
--   Let $a\leq b$. Suppose $f$ has derivative $f'(z)$
--   at every $z\in[a,b]$, $B$ is continuous on $[a,b]$, and
--   $|f'(z)|\leq B(z)$ there. Then
--   $$|f(b)-f(a)|\leq\int_a^b B(z)\,dz.$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Analysis/CoreIntegrals.lean#L86-L95

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

theorem BianchiIX.abs_sub_le_integral_bound {f f' B : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ∀ z ∈ Icc a b, HasDerivAt f (f' z) z) (hB : ContinuousOn B (Icc a b))
    (hbound : ∀ z ∈ Icc a b, |f' z| ≤ B z) :
    |f b - f a| ≤ ∫ z in a..b, B z := by sorry
