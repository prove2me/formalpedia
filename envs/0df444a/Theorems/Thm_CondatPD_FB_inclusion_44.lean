-- Prove2me | Theorems.Thm_CondatPD_FB_inclusion_44
-- name    : CondatPD.FB.inclusion_44
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T03:56:51.091097+00:00
-- url     : https://prove2.me/theorems/c7eb936b-aa1d-4700-83c8-a2e83e65c938
-- title:
--   Equation (44) — error-free Algorithm 3.2 satisfies the block inclusion
-- statement:
--   For the error-free proximal steps of Algorithm 3.2, let $\tilde y=\operatorname{prox}_{\sigma H^*}(y_n+\sigma Lx_n)$ and $\tilde x=\operatorname{prox}_{\tau G}(x_n-\tau\nabla F(x_n)-\tau L^*(2\tilde y-y_n))$. Under the paper's standing convexity assumptions and positive step sizes, their optimality conditions are
--   $$\sigma^{-1}(y_n-\tilde y)+Lx_n\in\partial H^*(\tilde y),$$
--   $$\tau^{-1}(x_n-\tilde x)-\nabla F(x_n)-L^*(2\tilde y-y_n)\in\partial G(\tilde x).$$
--
--   These two inclusions are equation (44) for the dual-first algorithm in rearranged form.
--
--   **Formalization Note** The standing $\Gamma_0$ assumptions justify the subgradient conclusions from the two proximal minima.
-- source:
--   Condat, A primal–dual splitting method for convex optimization involving Lipschitzian, proximable and linear composite terms, J. Optim. Theory Appl. 158(2) (2013), final author's version (HAL hal-00609728v5), p. 13, proof of Theorems 3.1–3.3 for Algorithm 3.2, (44)

import Mathlib
import Definitions.Def_CondatPD_FB_Setting

open InnerProductSpace

namespace CondatPD.FB

/-- Inclusion (44), p. 13, for Algorithm 3.2 in two-subgradient form. -/
theorem inclusion_44 {X Y : Type*} [NormedAddCommGroup X]
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
    let yt := PH (yn + σ • L xn)
    let xt := PG (xn - τ • gradient F xn -
      τ • ContinuousLinearMap.adjoint L ((2 : ℝ) • yt - yn))
    InertialFB.IFB.IsSubgradient (conj H) yt
      ((1 / σ) • (yn - yt) + L xn) ∧
    InertialFB.IFB.IsSubgradient G xt
      ((1 / τ) • (xn - xt) - gradient F xn -
        ContinuousLinearMap.adjoint L ((2 : ℝ) • yt - yn)) := by sorry

end CondatPD.FB
