-- Prove2me | Theorems.Thm_DavidonVM_Termination_grad_quad
-- name    : DavidonVM.Termination.grad_quad
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:42:58.083518+00:00
-- url     : https://prove2.me/theorems/7ae57a91-c212-419a-b98e-49a0ca147a1f
-- title:
--   Appendix (6) — the gradient of the quadratic with constant symmetric Hessian G is G(x − ξ)
-- statement:
--   Let $G$ be a symmetric real $n\times n$ matrix, $\xi\in\mathbb R^n$, $c\in\mathbb R$, and $f(x)=\tfrac12(x-\xi)^{\mathsf T}G(x-\xi)+c$. Then for every point $x$ and every direction $v$ the function $t\mapsto f(x+tv)$ is differentiable at $t=0$ with derivative
--   $$
--   \frac{d}{dt}\Big|_{t=0} f(x+tv)=\big(G(x-\xi)\big)^{\mathsf T}v .
--   $$
--   That is, the gradient of $f$ at $x$ is $\nabla=G(x-\xi)$, display (6) of the Appendix.
--
--   This ties the gradient field used by the method to the function being minimized: every statement about runs on the quadratic uses this field.
--
--   **Formalization Note** The paper says "When the G is constant, Δ can be written as $\nabla=G(x-\xi)$"; the "Δ" is a misprint for $\nabla$. The gradient is stated in directional-derivative form on `Fin n → ℝ`, for every direction. Symmetry of $G$ is assumed: for a nonsymmetric $G$ the gradient would be $\tfrac12(G+G^{\mathsf T})(x-\xi)$; the paper's $G$ is a Hessian, hence symmetric.
-- source:
--   Davidon, Variable Metric Method for Minimization, SIAM J. Optim. 1(1) (1991), p. 17, Appendix (6)

import Mathlib
import Definitions.Def_DavidonVM_Termination_Method

open Matrix

namespace DavidonVM.Termination

/-- Appendix (6), p. 17: for a quadratic with constant symmetric Hessian `G` and stationary
point `ξ`, the gradient is `∇ = G(x − ξ)`, stated as the derivative of `f` along every line
`t ↦ x + t v` at `t = 0`. -/
theorem grad_quad {n : ℕ} (G : Mat n) (hG : G.IsSymm) (ξ : Vec n) (c : ℝ) (x v : Vec n) :
    HasDerivAt (fun t : ℝ => quad G ξ c (x + t • v)) (grad G ξ x ⬝ᵥ v) 0 := by sorry

end DavidonVM.Termination
