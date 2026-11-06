-- Prove2me | Theorems.Thm_BianchiIX_exists_ode_local_contDiff_one
-- name    : BianchiIX.exists_ode_local_contDiff_one
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-04T23:10:14.270036+00:00
-- url     : https://prove2.me/theorems/38b50b60-fc5b-4c68-a743-b3976e95a453
-- title:
--   A continuously differentiable local family for a finite-dimensional ODE
-- statement:
--   Let $E$ be a finite-dimensional real normed space and
--   $f:E\to E$ be of class $C^2$. For every $x_0\in E$ and $t_0\in\mathbb R$
--   there exist $r,\varepsilon>0$ and $\alpha:E\times\mathbb R\to E$ such that
--   $\alpha$ is $C^1$ on $B(x_0,r)\times(t_0-\varepsilon,t_0+\varepsilon)$.
--   For every $x\in B(x_0,r)$,
--   $$\alpha(x,t_0)=x,\qquad
--   \partial_t\alpha(x,t)=f(\alpha(x,t))\quad(|t-t_0|<\varepsilon).$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Analysis/ODELocalFlow.lean#L102-L155

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
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.FDeriv.Partial

namespace BianchiIX
end BianchiIX

noncomputable section
open BianchiIX
open Set Filter Metric Asymptotics
open scoped Topology NNReal
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem BianchiIX.exists_ode_local_contDiff_one {f : E → E} (hf : ContDiff ℝ 2 f) (x₀ : E) (t₀ : ℝ) :
    ∃ r > (0 : ℝ), ∃ ε > (0 : ℝ), ∃ α : E × ℝ → E,
      ContDiffOn ℝ 1 α (ball x₀ r ×ˢ Ioo (t₀ - ε) (t₀ + ε)) ∧
      ∀ x ∈ ball x₀ r, α (x, t₀) = x ∧
        ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε), HasDerivAt (fun u => α (x, u)) (f (α (x, t))) t := by sorry
