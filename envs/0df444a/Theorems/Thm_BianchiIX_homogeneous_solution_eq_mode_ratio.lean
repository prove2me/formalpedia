-- Prove2me | Theorems.Thm_BianchiIX_homogeneous_solution_eq_mode_ratio
-- name    : BianchiIX.homogeneous_solution_eq_mode_ratio
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-04T21:51:22.867861+00:00
-- url     : https://prove2.me/theorems/29d46285-3943-4512-a7ad-d23f15cd21eb
-- title:
--   Recovery of a scalar homogeneous solution from a nonzero mode
-- statement:
--   Let $I\subset\mathbb R$ be convex. Suppose
--   $f'(u)=a(u)f(u)$ and $g'(u)=a(u)g(u)$ for every $u\in I$,
--   with $g(u)\ne0$ on $I$. For all $s,t\in I$,
--   $$f(t)=f(s)\frac{g(t)}{g(s)}.$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Dynamics/ReferenceVariation.lean#L47-L59

import Definitions.Def_BianchiIX_Dynamics_ReferenceVariation
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.ODE.ExistUnique

noncomputable section
open BianchiIX
open Set

theorem BianchiIX.homogeneous_solution_eq_mode_ratio {I : Set ℝ} (hI : Convex ℝ I)
    {f g a : ℝ → ℝ} (hf : ∀ t ∈ I, HasDerivAt f (a t * f t) t)
    (hg : ∀ t ∈ I, HasDerivAt g (a t * g t) t) (hzero : ∀ t ∈ I, g t ≠ 0)
    {s t : ℝ} (hs : s ∈ I) (ht : t ∈ I) : f t = f s * (g t / g s) := by sorry
