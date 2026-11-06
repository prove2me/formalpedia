-- Prove2me | Theorems.Thm_BianchiIX_integral_clock_le_of_cosh_sq
-- name    : BianchiIX.integral_clock_le_of_cosh_sq
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-05T02:30:11.857518+00:00
-- url     : https://prove2.me/theorems/1ecad01f-7167-428f-a790-4ad58f0ea492
-- title:
--   An endpoint bound for a squared-cosh envelope in a monotone clock
-- statement:
--   Let $a\leq b$, $B\geq0$, and let $f,\omega$
--   be continuous on $[a,b]$. Suppose throughout this interval that
--   $z'(t)=\omega(t)\geq0$ and $f(t)\leq B\cosh^2 z(t)$.
--   If $\cosh z(a),\cosh z(b)\leq K$, then
--   $$\int_a^b f(t)\omega(t)\,dt\leq2BK^2.$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Analysis/ClockWeightIntegrals.lean#L9-L23

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

theorem BianchiIX.integral_clock_le_of_cosh_sq {f z rate : ℝ → ℝ} {a b B K : ℝ}
    (hab : a ≤ b) (hz : ∀ t ∈ Icc a b, HasDerivAt z (rate t) t)
    (hrate : ContinuousOn rate (Icc a b)) (hpos : ∀ t ∈ Icc a b, 0 ≤ rate t)
    (hB : 0 ≤ B) (hf : ContinuousOn f (Icc a b))
    (hbound : ∀ t ∈ Icc a b, f t ≤ B * Real.cosh (z t) ^ 2)
    (ha : Real.cosh (z a) ≤ K) (hb : Real.cosh (z b) ≤ K) :
    (∫ t in a..b, f t * rate t) ≤ 2 * B * K ^ 2 := by sorry
