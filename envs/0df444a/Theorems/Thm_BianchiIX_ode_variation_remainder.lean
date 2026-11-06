-- Prove2me | Theorems.Thm_BianchiIX_ode_variation_remainder
-- name    : BianchiIX.ode_variation_remainder
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-04T23:07:21.978439+00:00
-- url     : https://prove2.me/theorems/949efd6b-fbc8-44e4-8e0a-3f04bbf7eec0
-- title:
--   A quadratic nonlinear remainder for a general variational equation
-- statement:
--   For real $\delta,K,\varepsilon,\ell$, let
--   $$G(\delta,K,\varepsilon,\ell)=
--   \begin{cases}
--   \delta+\varepsilon\ell,&K=0,\\
--   \delta e^{K\ell}+\varepsilon(e^{K\ell}-1)/K,&K\ne0.
--   \end{cases}$$
--   Write $[s,t]_{\mathrm{u}}=[\min(s,t),\max(s,t)]$.
--   Let $E$ be a real normed space, $f:E\to E$,
--   and $D:E\to\mathcal L(E,E)$, with $df_x=D(x)$ for every $x\in E$.
--   Let $S\subset E$ be convex and $D$ be $C$-Lipschitz on $S$, with $C\geq0$.
--   Suppose $\alpha,\beta$ solve $u'=f(u)$ and remain in $S$ on
--   $[t_0,t]_{\mathrm u}$. Assume
--   $$J'=D(\alpha)\circ J,\qquad J(t_0)=\operatorname{id}_E,$$
--   and, throughout that interval,
--   $$\|D(\alpha(u))\|\leq K,\qquad
--   \|\beta(u)-\alpha(u)\|\leq L\|\beta(t_0)-\alpha(t_0)\|.$$
--   For $h=\beta(t_0)-\alpha(t_0)$ one has
--   $$\|\beta(t)-\alpha(t)-J(t)h\|
--   \leq G(0,K,CL^2,|t-t_0|)\|h\|^2.$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Analysis/ODEVariation.lean#L49-L87

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

namespace BianchiIX
end BianchiIX

noncomputable section
open BianchiIX
open Set Filter Metric Asymptotics
open scoped Topology NNReal
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem BianchiIX.ode_variation_remainder {f : E → E} {D : E → E →L[ℝ] E}
    (hf : ∀ x, HasFDerivAt f (D x) x) {α β : ℝ → E} {J : ℝ → E →L[ℝ] E}
    {t₀ t : ℝ} {S : Set E} (hS : Convex ℝ S) {K L : ℝ} {C : ℝ≥0}
    (hD : LipschitzOnWith C D S)
    (hα : ∀ u ∈ uIcc t₀ t, HasDerivAt α (f (α u)) u)
    (hβ : ∀ u ∈ uIcc t₀ t, HasDerivAt β (f (β u)) u)
    (hαS : ∀ u ∈ uIcc t₀ t, α u ∈ S) (hβS : ∀ u ∈ uIcc t₀ t, β u ∈ S)
    (hJ : ∀ u ∈ uIcc t₀ t, HasDerivAt J ((D (α u)).comp (J u)) u)
    (hJinit : J t₀ = ContinuousLinearMap.id ℝ E)
    (hDnorm : ∀ u ∈ uIcc t₀ t, ‖D (α u)‖ ≤ K)
    (hclose : ∀ u ∈ uIcc t₀ t, ‖β u - α u‖ ≤ L * ‖β t₀ - α t₀‖) :
    ‖β t - α t - J t (β t₀ - α t₀)‖ ≤
      gronwallBound 0 K (C * L ^ 2) |t - t₀| * ‖β t₀ - α t₀‖ ^ 2 := by sorry
