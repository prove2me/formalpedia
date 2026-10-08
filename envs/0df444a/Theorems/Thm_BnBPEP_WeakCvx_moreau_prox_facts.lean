-- Prove2me | Theorems.Thm_BnBPEP_WeakCvx_moreau_prox_facts
-- name    : BnBPEP.WeakCvx.moreau_prox_facts
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:47:37.548521+00:00
-- url     : https://prove2.me/theorems/b4c3c2b6-4f48-4837-b1e0-0e3aace1214b
-- title:
--   §6.3.1 — the prox point gives $f_{(1/\hat\rho)}(x)$, $\nabla f_{(1/\hat\rho)}(x)=\hat\rho(x-y)\in\partial f(y)$
-- statement:
--   Let $L>0$ and $f\in\mathcal W_{1,L}$, i.e. $f+\frac12\|\cdot\|^2$ is convex on $\mathbb R^d$ and all subgradients of $f$ have norm at most $L$. Let $\hat\rho>1$, let $x\in\mathbb R^d$, and let $y=\mathrm{prox}_{(1/\hat\rho)f}(x)$ be a minimizer of $z\mapsto f(z)+\frac{\hat\rho}{2}\|z-x\|^2$. Then
--
--   1. the Moreau envelope attains its defining infimum at $y$: $\;f_{(1/\hat\rho)}(x)=f(y)+\frac{\hat\rho}{2}\|y-x\|^2$;
--   2. it is a global underestimator: $f_{(1/\hat\rho)}(x)\le f(x)$;
--   3. $f_{(1/\hat\rho)}$ is continuously differentiable on $\mathbb R^d$;
--   4. its gradient at $x$ is given by the prox point and is a subgradient of $f$ at $y$:
--   $$\nabla f_{(1/\hat\rho)}(x)=\hat\rho\,(x-y)\ \in\ \partial f(y),$$
--   where $g\in\partial f(y)$ means $f(z)\ge f(y)+\langle g,z-y\rangle-\frac12\|z-y\|^2$ for all $z$.
--
--   These facts are what make $\|\nabla f_{(1/2)}(x)\|^2$ a computable stationarity measure: with $\hat\rho=2$ they give $\nabla f_{(1/2)}(x_i)=2(x_i-y_i)=f'(y_i)$, the identity (31) on which the potential-function analysis of the subgradient method rests.
--
--   **Formalization Note** The paper's display reads $x-y=\frac1{\hat\rho}\nabla f_{(1/\hat\rho)}(x)\in\partial f(y)$; the membership is that of the gradient $\nabla f_{(1/\hat\rho)}(x)=\hat\rho(x-y)$, as (31) uses it ($f'(y_i)=2(x_i-y_i)$ for $\hat\rho=2$), and this is what is stated. The prox point is a hypothesis (`IsProxPoint f (1/ρ̂) x y`, weight $\frac{1}{2\cdot(1/\hat\rho)}=\frac{\hat\rho}{2}$); for $\hat\rho>1$ it exists and is unique. The subdifferential is the weak-convexity inequality with modulus $1$.
-- source:
--   Das Gupta, Van Parys, Ryu, Branch-and-bound performance estimation programming, Math. Program. 204 (2024), §6.3.1, p. 614 (display x − y = (1/ρ̂)∇f_{(1/ρ̂)}(x) ∈ ∂f(y), citing [68, (2.13), (2.17)])

import Mathlib
import Definitions.Def_SAGA_Convex_IsProxPoint
import Definitions.Def_BnBPEP_WeakCvx_IsWeakSubgrad
import Definitions.Def_BnBPEP_WeakCvx_InWeakClass
import Definitions.Def_BnBPEP_WeakCvx_moreauEnv

namespace BnBPEP.WeakCvx

/-- §6.3.1, p. 614: for `f ∈ W_{1,L}` and `ρ̂ > 1`, with `y = prox_{(1/ρ̂)f}(x)`, the Moreau
envelope `f_{(1/ρ̂)}` attains its defining minimum at `y`, underestimates `f`, is continuously
differentiable, and `∇f_{(1/ρ̂)}(x) = ρ̂ (x - y) ∈ ∂f(y)`. -/
theorem moreau_prox_facts {d : ℕ} (f : EuclideanSpace ℝ (Fin d) → ℝ) (L ρhat : ℝ)
    (hL : 0 < L) (hf : InWeakClass 1 L f) (hρ : 1 < ρhat)
    (x y : EuclideanSpace ℝ (Fin d)) (hy : SAGA.Convex.IsProxPoint f (1 / ρhat) x y) :
    moreauEnv ρhat f x = f y + ρhat / 2 * ‖y - x‖ ^ 2 ∧
      moreauEnv ρhat f x ≤ f x ∧
      ContDiff ℝ 1 (moreauEnv ρhat f) ∧
      HasGradientAt (moreauEnv ρhat f) (ρhat • (x - y)) x ∧
      IsWeakSubgrad 1 f y (ρhat • (x - y)) := by sorry

end BnBPEP.WeakCvx
