-- Prove2me | Theorems.Thm_BianchiIX_exists_ode_local_contDiff_succ
-- name    : BianchiIX.exists_ode_local_contDiff_succ
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-04T23:11:14.135284+00:00
-- url     : https://prove2.me/theorems/63c279f6-1caa-4f00-bd29-e16fc0bb445e
-- title:
--   Arbitrarily high finite regularity of local solution families
-- statement:
--   For every $n\in\mathbb N$, every finite-dimensional real
--   normed space $E$, every smooth vector field $f:E\to E$, and every
--   $(x_0,t_0)\in E\times\mathbb R$, there exist $r,\varepsilon>0$ and
--   $\alpha:E\times\mathbb R\to E$ of class $C^{n+1}$ on
--   $B(x_0,r)\times(t_0-\varepsilon,t_0+\varepsilon)$ such that
--   $$\alpha(x,t_0)=x,\qquad
--   \partial_t\alpha(x,t)=f(\alpha(x,t))$$
--   for $x\in B(x_0,r)$ and $|t-t_0|<\varepsilon$.
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Analysis/ODESmoothFlow.lean#L12-L90

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
open Set Filter Metric
open scoped Topology NNReal ContDiff
universe u

theorem BianchiIX.exists_ode_local_contDiff_succ (n : ℕ) :
    ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
      {f : E → E}, ContDiff ℝ ∞ f → ∀ (x₀ : E) (t₀ : ℝ),
      ∃ r > (0 : ℝ), ∃ ε > (0 : ℝ), ∃ α : E × ℝ → E,
        ContDiffOn ℝ (n + 1) α (ball x₀ r ×ˢ Ioo (t₀ - ε) (t₀ + ε)) ∧
        ∀ x ∈ ball x₀ r, α (x, t₀) = x ∧
          ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε), HasDerivAt (fun u => α (x, u)) (f (α (x, t))) t := by sorry
