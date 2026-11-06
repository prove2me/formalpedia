-- Prove2me | Theorems.Thm_BianchiIX_core_forced_variation_integrals
-- name    : BianchiIX.core_forced_variation_integrals
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-05T01:58:05.057523+00:00
-- url     : https://prove2.me/theorems/240fd1a5-6b5a-4484-be53-13bcb2243f62
-- title:
--   Two duration-independent integral bounds for a forced core variation
-- statement:
--   Let $k\geq6$, $T\geq0$, $U,Q\geq0$, and
--   $\cosh z_0=k$. Suppose $x$ is continuous on $[0,T]$ and
--   $$|x(t)|\leq e^{-kt/4}(|x(0)|+3kUQt)\qquad(0\leq t\leq T).$$
--   Then
--   $$\int_0^T\frac{|x(t)|}{\cosh(z_0+t)}\,dt
--   \leq\frac{12|x(0)|+432UQ}{k^2},$$
--   $$\int_0^T|x(t)|\,dt\leq\frac{4|x(0)|+48UQ}{k}.$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Analysis/ForcedDecayIntegrals.lean#L44-L89

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

theorem BianchiIX.core_forced_variation_integrals {x : ℝ → ℝ} {k T z₀ U Q : ℝ}
    (hk : 6 ≤ k) (hT : 0 ≤ T) (hU : 0 ≤ U) (hQ : 0 ≤ Q)
    (hx : ContinuousOn x (Icc 0 T)) (hz₀ : Real.cosh z₀ = k)
    (hbound : ∀ t ∈ Icc 0 T,
      |x t| ≤ Real.exp (-k * t / 4) * (|x 0| + 3 * k * U * Q * t)) :
    (∫ t in 0..T, |x t| / Real.cosh (z₀ + t)) ≤ (12 * |x 0| + 432 * U * Q) / k ^ 2 ∧
      (∫ t in 0..T, |x t|) ≤ (4 * |x 0| + 48 * U * Q) / k := by sorry
