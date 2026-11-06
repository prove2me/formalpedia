-- Prove2me | Theorems.Thm_BianchiIX_abs_bounds_of_forced_derivative_feedback
-- name    : BianchiIX.abs_bounds_of_forced_derivative_feedback
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-05T07:05:12.697208+00:00
-- url     : https://prove2.me/theorems/afe6e412-41bb-48cf-8135-f53c32991bad
-- title:
--   A feedback integral below one can be absorbed into a uniform bound
-- statement:
--   Let $a\leq b$, let $f$ have derivative $f'$ on $[a,b]$,
--   and let $k,e$ be continuous and nonnegative there. Suppose
--   $\int_a^b k\leq\Lambda<1$. Assume that whenever $Q\geq0$ bounds
--   $|f|$ on the whole interval, one has $|f'(t)|\leq e(t)+k(t)Q$
--   there. Set $E=\int_a^b e$ and $M=(|f(a)|+E)/(1-\Lambda)$. Then
--   $$|f(t)|\leq M,\qquad |f(t)-f(a)|\leq E+\Lambda M\quad(t\in[a,b]).$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Analysis/FeedbackAbsorption.lean#L9-L53

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

theorem BianchiIX.abs_bounds_of_forced_derivative_feedback {f f' k e : ℝ → ℝ} {a b Λ : ℝ}
    (hab : a ≤ b) (hf : ∀ t ∈ Icc a b, HasDerivAt f (f' t) t)
    (hk : ContinuousOn k (Icc a b)) (hk0 : ∀ t ∈ Icc a b, 0 ≤ k t)
    (he : ContinuousOn e (Icc a b)) (he0 : ∀ t ∈ Icc a b, 0 ≤ e t)
    (hbudget : (∫ t in a..b, k t) ≤ Λ) (hΛ : Λ < 1)
    (hfeedback : ∀ Q : ℝ, 0 ≤ Q → (∀ t ∈ Icc a b, |f t| ≤ Q) →
      ∀ t ∈ Icc a b, |f' t| ≤ e t + k t * Q) :
    ∀ t ∈ Icc a b, |f t| ≤ (|f a| + ∫ s in a..b, e s) / (1 - Λ) ∧
      |f t - f a| ≤ (∫ s in a..b, e s) + Λ * (|f a| + ∫ s in a..b, e s) / (1 - Λ) := by sorry
