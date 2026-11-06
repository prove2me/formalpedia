-- Prove2me | Theorems.Thm_BianchiIX_image_sub_le_clock_sub_of_deriv_le
-- name    : BianchiIX.image_sub_le_clock_sub_of_deriv_le
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-05T00:33:54.12382+00:00
-- url     : https://prove2.me/theorems/a5a8a1dd-5d4f-4746-9031-37a36782a752
-- title:
--   Comparing displacement with a differentiable clock increment
-- statement:
--   Let $I\subset\mathbb R$ be convex, $s,t\in I$,
--   $s\leq t$, and $C\in\mathbb R$. Suppose real functions $f,z$ have
--   derivatives on $I$ with $f'(q)\leq C z'(q)$ there. Then
--   $$f(t)-f(s)\leq C(z(t)-z(s)).$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Dynamics/CoreTraversal.lean#L11-L23

import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
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

theorem BianchiIX.image_sub_le_clock_sub_of_deriv_le {I : Set ℝ} (hI : Convex ℝ I)
    {f f' z z' : ℝ → ℝ} {C s t : ℝ}
    (hf : ∀ u ∈ I, HasDerivAt f (f' u) u) (hz : ∀ u ∈ I, HasDerivAt z (z' u) u)
    (hbound : ∀ u ∈ I, f' u ≤ C * z' u)
    (hs : s ∈ I) (ht : t ∈ I) (hst : s ≤ t) :
    f t - f s ≤ C * (z t - z s) := by sorry
