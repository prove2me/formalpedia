-- Prove2me | Theorems.Thm_CondatPD_FB_inclusion_22
-- name    : CondatPD.FB.inclusion_22
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T03:56:48.197245+00:00
-- url     : https://prove2.me/theorems/7dc9e59e-aa60-434a-8bec-d0386cc29a46
-- title:
--   Equation (22) — error-free Algorithm 3.1 satisfies the block inclusion
-- statement:
--   For the error-free proximal steps of Algorithm 3.1, let $\tilde x=\operatorname{prox}_{\tau G}(x_n-\tau\nabla F(x_n)-\tau L^*y_n)$ and $\tilde y=\operatorname{prox}_{\sigma H^*}(y_n+\sigma L(2\tilde x-x_n))$. Under the paper's standing convexity assumptions and positive step sizes, their proximal optimality conditions are
--   $$\tau^{-1}(x_n-\tilde x)-\nabla F(x_n)-L^*y_n\in\partial G(\tilde x),$$
--   $$\sigma^{-1}(y_n-\tilde y)+L(2\tilde x-x_n)\in\partial H^*(\tilde y).$$
--
--   Together these are the two rows of inclusion (22), after moving its linear terms across.
--
--   **Formalization Note** The hypotheses that $G,H\in\Gamma_0$ are needed to derive subgradients from proximal minimizers; they are the standing assumptions of §2.
-- source:
--   Condat, A primal–dual splitting method for convex optimization involving Lipschitzian, proximable and linear composite terms, J. Optim. Theory Appl. 158(2) (2013), final author's version (HAL hal-00609728v5), p. 10, proof of Theorem 3.1, (22)

import Mathlib
import Definitions.Def_CondatPD_FB_Setting

open InnerProductSpace

namespace CondatPD.FB

/-- Inclusion (22), p. 10, in its equivalent two-subgradient form. -/
theorem inclusion_22 {X Y : Type*} [NormedAddCommGroup X]
    [InnerProductSpace ℝ X] [CompleteSpace X] [NormedAddCommGroup Y]
    [InnerProductSpace ℝ Y] [CompleteSpace Y]
    (F : X → ℝ) (G : X → EReal) (H : Y → EReal) (L : X →L[ℝ] Y)
    (PG : X → X) (PH : Y → Y) (β τ σ : ℝ)
    (hF : IsSmoothTerm β F)
    (hG : ThreeOpSplitting.ConvexRates.IsProperClosedConvex G)
    (hH : ThreeOpSplitting.ConvexRates.IsProperClosedConvex H)
    (hτ : 0 < τ) (hσ : 0 < σ)
    (hPG : ThreeOpSplitting.ConvexRates.IsProx τ G PG)
    (hPH : ThreeOpSplitting.ConvexRates.IsProx σ (conj H) PH)
    (xn : X) (yn : Y) :
    let xt := PG (xn - τ • gradient F xn - τ • ContinuousLinearMap.adjoint L yn)
    let yt := PH (yn + σ • L ((2 : ℝ) • xt - xn))
    InertialFB.IFB.IsSubgradient G xt
      ((1 / τ) • (xn - xt) - gradient F xn - ContinuousLinearMap.adjoint L yn) ∧
    InertialFB.IFB.IsSubgradient (conj H) yt
      ((1 / σ) • (yn - yt) + L ((2 : ℝ) • xt - xn)) := by sorry

end CondatPD.FB
