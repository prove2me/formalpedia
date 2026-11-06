-- Prove2me | Theorems.Thm_BianchiIX_contDiffOn_ode_family_with_derivative
-- name    : BianchiIX.contDiffOn_ode_family_with_derivative
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-04T23:08:29.935198+00:00
-- url     : https://prove2.me/theorems/ae89ecef-93c0-45e7-9f81-8f7100b150f3
-- title:
--   A continuous variational family gives the strict derivative of the flow
-- statement:
--   Let $E$ be a finite-dimensional real normed space and
--   $f:E\to E$ be of class $C^2$. Fix $x_0\in E$, $t_0,r\in\mathbb R$,
--   $\varepsilon>0$, and $L\geq0$. Write
--   $$I=(t_0-\varepsilon,t_0+\varepsilon),\quad
--   U=B(x_0,r)\times I,\quad
--   K=\overline B(x_0,r)\times[t_0-\varepsilon,t_0+\varepsilon].$$
--   Suppose $\alpha:E\times\mathbb R\to E$ is continuous on $K$ and
--   $J:E\times\mathbb R\to\mathcal L(E,E)$ is continuous on $U$.
--   For $x\in B(x_0,r)$ assume
--   $$\alpha(x,t_0)=x,\qquad J(x,t_0)=\operatorname{id}_E,$$
--   $$\partial_t\alpha(x,t)=f(\alpha(x,t)),\qquad
--   \partial_tJ(x,t)=df_{\alpha(x,t)}\circ J(x,t)\quad(t\in I).$$
--   Each fixed-time map $x\mapsto\alpha(x,t)$ is $L$-Lipschitz on $B(x_0,r)$.
--   The solution family $\alpha$ is of class
--   $C^1$ on $U$. At every $(x,t)\in U$ it is strictly Frechet differentiable,
--   with derivative
--   $$d\alpha_{(x,t)}(v,s)=J(x,t)v+s f(\alpha(x,t)).$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Analysis/ODELocalFlow.lean#L14-L84

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

theorem BianchiIX.contDiffOn_ode_family_with_derivative {f : E → E} (hf : ContDiff ℝ 2 f)
    {x₀ : E} {t₀ r ε : ℝ} (hε : 0 < ε)
    {α : E × ℝ → E} {J : E × ℝ → E →L[ℝ] E} {L : ℝ≥0}
    (hcα : ContinuousOn α (closedBall x₀ r ×ˢ Icc (t₀ - ε) (t₀ + ε)))
    (hcJ : ContinuousOn J (ball x₀ r ×ˢ Ioo (t₀ - ε) (t₀ + ε)))
    (hα0 : ∀ x ∈ ball x₀ r, α (x, t₀) = x)
    (hJ0 : ∀ x ∈ ball x₀ r, J (x, t₀) = ContinuousLinearMap.id ℝ E)
    (hα : ∀ x ∈ ball x₀ r, ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε),
      HasDerivAt (fun u => α (x, u)) (f (α (x, t))) t)
    (hJ : ∀ x ∈ ball x₀ r, ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε),
      HasDerivAt (fun u => J (x, u)) ((fderiv ℝ f (α (x, t))).comp (J (x, t))) t)
    (hLip : ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε),
      LipschitzOnWith L (fun x => α (x, t)) (ball x₀ r)) :
    ContDiffOn ℝ 1 α (ball x₀ r ×ˢ Ioo (t₀ - ε) (t₀ + ε)) ∧
      ∀ z ∈ ball x₀ r ×ˢ Ioo (t₀ - ε) (t₀ + ε), HasStrictFDerivAt α
        ((J z).coprod ((ContinuousLinearMap.id ℝ ℝ).smulRight (f (α z)))) z := by sorry
