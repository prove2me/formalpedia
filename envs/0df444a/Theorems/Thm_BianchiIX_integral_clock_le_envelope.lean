-- Prove2me | Theorems.Thm_BianchiIX_integral_clock_le_envelope
-- name    : BianchiIX.integral_clock_le_envelope
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-05T01:54:48.035254+00:00
-- url     : https://prove2.me/theorems/ed4ef5dc-7cab-4255-82d9-ee74c3461d6c
-- title:
--   Transport of an integral envelope through a nondecreasing differentiable clock
-- statement:
--   Let $a\leq b$, let $f$ and $\omega$ be continuous
--   on $[a,b]$, and let $G:\mathbb R\to\mathbb R$ be continuous.
--   Suppose on $[a,b]$ that $z'(t)=\omega(t)\geq0$ and
--   $f(t)\leq G(z(t))$. Then
--   $$\int_a^b f(t)\omega(t)\,dt\leq\int_{z(a)}^{z(b)}G(s)\,ds.$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Analysis/ClockEnvelope.lean#L10-L25

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

theorem BianchiIX.integral_clock_le_envelope {f z rate G : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hz : ∀ t ∈ Icc a b, HasDerivAt z (rate t) t)
    (hrate : ContinuousOn rate (Icc a b)) (hpos : ∀ t ∈ Icc a b, 0 ≤ rate t)
    (hf : ContinuousOn f (Icc a b)) (hG : Continuous G)
    (hbound : ∀ t ∈ Icc a b, f t ≤ G (z t)) :
    (∫ t in a..b, f t * rate t) ≤ ∫ s in z a..z b, G s := by sorry
