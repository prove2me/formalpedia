-- Prove2me | Theorems.Thm_BianchiIX_le_exp_of_clock_deriv_le
-- name    : BianchiIX.le_exp_of_clock_deriv_le
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-05T00:01:34.88095+00:00
-- url     : https://prove2.me/theorems/92b87928-a27a-478e-bc0f-c961ec106b14
-- title:
--   Scalar exponential comparison in a differentiable clock
-- statement:
--   Let $I\subset\mathbb R$ be convex, $s,t\in I$,
--   $s\leq t$, and $c\in\mathbb R$. Suppose real functions $f,z$
--   have derivatives $f'(q),z'(q)$ at every $q\in I$ and satisfy
--   $$f'(q)\leq c z'(q)f(q)\quad(q\in I).$$
--   Then
--   $$f(t)\leq f(s)\exp\bigl(c(z(t)-z(s))\bigr).$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Dynamics/CoreContraction.lean#L10-L37

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

namespace BianchiIX
end BianchiIX

noncomputable section
open BianchiIX
open Set

theorem BianchiIX.le_exp_of_clock_deriv_le {I : Set ℝ} (hI : Convex ℝ I)
    {f f' z z' : ℝ → ℝ} {c s t : ℝ}
    (hf : ∀ u ∈ I, HasDerivAt f (f' u) u) (hz : ∀ u ∈ I, HasDerivAt z (z' u) u)
    (hbound : ∀ u ∈ I, f' u ≤ c * z' u * f u)
    (hs : s ∈ I) (ht : t ∈ I) (hst : s ≤ t) :
    f t ≤ f s * Real.exp (c * (z t - z s)) := by sorry
