-- Prove2me | Theorems.Thm_CoVaRMC_Batching_cond_density
-- name    : CoVaRMC.Batching.cond_density
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T23:08:51.642335+00:00
-- url     : https://prove2.me/theorems/7ffd9f9c-a3a4-49d6-98ff-511647ccf32d
-- title:
--   p. 5 — for x ∈ 𝒳, F_{Y|X}(y|x) is differentiable in y ∈ 𝒴 with derivative f(x, y)/f_X(x) > 0
-- statement:
--   Let $(X, Y)$ have joint density $f$, marginal density $f_X$, and let $F_c$ be a version of the conditional distribution function $F_{Y|X}(y\mid x)$ of Equation (3), i.e. $F_c(y, x) = \int_{-\infty}^y f(x,v)/f_X(x)\,dv$ whenever $f_X(x) > 0$. Suppose Assumption 1 holds with neighbourhoods $\mathcal X \ni v$ and $\mathcal Y \ni c$. Then for every $x \in \mathcal X$ and every $y \in \mathcal Y$, the function $y \mapsto F_{Y|X}(y\mid x)$ is differentiable at $y$, and the conditional density satisfies
--   $$f_{Y|X}(y\mid x) = \frac{\partial}{\partial y} F_{Y|X}(y\mid x) = \frac{f(x,y)}{f_X(x)} > 0.$$
--
--   This is the fact that makes CoVaR the unique solution of (2) and that supplies the constant $f_{Y|X}(\mathrm{CoVaR}_{\alpha,\beta}\mid \mathrm{VaR}_\alpha(X))$ in the limit variance of Theorem 3.
--
--   **Formalization Note.** The statement does not need $v = \mathrm{VaR}_\alpha(X)$ or $c = \mathrm{CoVaR}_{\alpha,\beta}$: it holds for whatever points Assumption 1 is centred at, so equations (1) and (2) are not assumed (this only strengthens it). Differentiability is claimed only at $y \in \mathcal Y$, as on the page.
-- source:
--   Huang, Lin, Hong, Monte-Carlo Estimation of CoVaR, arXiv:2210.06148v1, p. 5, 'for x ∈ 𝒳, F_{Y|X}(y|x) is a differentiable function of y'

import Mathlib
import Definitions.Def_CoVaRMC_Batching_Setting

open MeasureTheory ProbabilityTheory Filter Topology

namespace CoVaRMC.Batching

/-- p. 5: under Assumption 1, for `x ∈ 𝒳`, `y ↦ F_{Y|X}(y | x)` is differentiable at every `y ∈ 𝒴`
with derivative `f_{Y|X}(y | x) = f(x, y) / f_X(x) > 0`. -/
theorem cond_density (D : JointDensity) (Fc : ℝ → ℝ → ℝ) (v c : ℝ) (𝒳 𝒴 : Set ℝ)
    (hFc : IsCondCDFVersion D Fc) (hA1 : Assumption1 D Fc v c 𝒳 𝒴)
    (x : ℝ) (hx : x ∈ 𝒳) (y : ℝ) (hy : y ∈ 𝒴) :
    HasDerivAt (fun y' => Fc y' x) (D.condDensity y x) y ∧ 0 < D.condDensity y x := by sorry

end CoVaRMC.Batching
