-- Prove2me | Theorems.Thm_DissolveCDF_proposition_3_8
-- name    : DissolveCDF.proposition_3_8
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:32:22.567075+00:00
-- url     : https://prove2.me/theorems/48a29400-822c-4073-952c-b5095edaa225
-- title:
--   Proposition 3.8 — gradient and Hessian of the CDF (corrected: Hessian terms read as $\sum_k\partial_kf(\mathcal A(x))\nabla^2\mathcal A_k(x)$ and $\sum_i c_i(x)\nabla^2c_i(x)$)
-- statement:
--   Throughout, $f:\mathbb R^n\to\mathbb R$ is the objective and $c:\mathbb R^n\to\mathbb R^p$ the constraint map of the problem (OCP) $\min_x f(x)$ s.t. $c(x)=0$, with feasible set $\mathcal M=\{x: c(x)=0\}$; $\mathcal A:\mathbb R^n\to\mathbb R^n$ is a constraint dissolving operator, and $f,c,\mathcal A$ satisfy Assumptions 1.1 and 1.2.
--
--   Let $g(x):=f(\mathcal A(x))$ and $h(x)=g(x)+\frac\beta2\|c(x)\|^2$.
--
--   1. For every $\beta\in\mathbb R$ and $x\in\mathbb R^n$,
--
--   $$
--   \nabla h(x)=J_{\mathcal A}(x)\nabla f(\mathcal A(x))+\beta J_c(x)c(x). \tag{3.8}
--   $$
--
--   2. If moreover $f$, $c$ and $\mathcal A$ are twice differentiable (Assumption 2.11), then for every $\beta$ and $x$,
--
--   $$
--   \nabla^2g(x)=J_{\mathcal A}(x)\nabla^2f(\mathcal A(x))J_{\mathcal A}(x)^\top+\sum_{k=1}^n\partial_kf(\mathcal A(x))\,\nabla^2\mathcal A_k(x), \tag{3.9}
--   $$
--
--   $$
--   \nabla^2h(x)=\nabla^2g(x)+\beta\Big(J_c(x)J_c(x)^\top+\sum_{i=1}^p c_i(x)\,\nabla^2c_i(x)\Big). \tag{3.10}
--   $$
--
--   The gradient of $h$ needs only $\nabla f$ (unlike Fletcher's penalty), and its Hessian only $\nabla^2f$.
--
--   **Formalization Note** The Hessian of $\varphi$ at $x$ is the derivative of $\nabla\varphi$ at $x$. "Twice differentiable" is: the derivative maps of $f$, $c$, $\mathcal A$ are differentiable (no continuity of second derivatives).
--
--   Differences from the source:
--   - correction: (3.9): ∇²g(x) = J_A(x)∇²f(A(x))J_A(x)ᵀ + D_{J_A}(x)[∇f(A(x))], with D_{J_A}(x)[d] the directional derivative of J_A along d (p.5) → the second term is Σₖ ∂ₖf(A(x)) ∇²Aₖ(x), i.e. d ↦ (D_{J_A}(x)[d]) ∇f(A(x)); reason: read literally, (3.9) is false: n = 2, p = 1, c(x) = x₂, A(x) = (x₁ + x₂², x₂²), f(y) = y₁ satisfy Assumptions 1.1, 1.2 and 2.11, ∇²g = diag(0, 2), but J_A does not depend on x₁ and ∇²f = 0, so the literal right side is 0; the chain rule gives the stated sum
--   - reading: (3.10): β(J_c(x)J_c(x)ᵀ + D_{J_c}(x)[c(x)]) → β(J_c(x)J_c(x)ᵀ + Σᵢ cᵢ(x) ∇²cᵢ(x)); reason: D_{J_c}(x)[c(x)] with c(x) ∈ ℝᵖ as a direction in ℝⁿ is ill-typed for p ≠ n; the chain rule gives the stated sum
--   - encoding: Assumption 2.11: f, c and A are twice differentiable in ℝⁿ → Differentiable ℝ (fderiv ℝ f), Differentiable ℝ (fderiv ℝ c), Differentiable ℝ (fderiv ℝ A); reason: twice (Fréchet) differentiable, no continuity of the second derivative
--   - encoding: ∇²φ(x) → fderiv ℝ (gradient φ) x; reason: the Hessian as the derivative of the gradient map
-- source:
--   Xiao, Liu & Toh, Dissolving Constraints for Riemannian Optimization, arXiv:2203.10319v3, Proposition 3.8, (3.8)–(3.10), p.10; Assumption 2.11, p.8; notation D_{J_A}, D_{J_c}, §2.1, p.5

import Mathlib
import Definitions.Def_DissolveCDF_Assumption11
import Definitions.Def_DissolveCDF_Assumption12
import Definitions.Def_DissolveCDF_transJac
import Definitions.Def_DissolveCDF_cdf

namespace DissolveCDF

/-- Xiao, Liu & Toh, *Dissolving Constraints for Riemannian Optimization*, arXiv:2203.10319v3, Proposition 3.8, p.10 (corrected reading of the Hessian terms): the gradient of
`h` is `∇h(x) = J_A(x)∇f(A(x)) + βJ_c(x)c(x)` (3.8). Furthermore, under Assumption 2.11 (`f`, `c`
and `A` twice differentiable), the Hessian of `g(x) := f(A(x))` is
`∇²g(x) = J_A(x)∇²f(A(x))J_A(x)ᵀ + Σₖ ∂ₖf(A(x)) ∇²Aₖ(x)` (3.9) and the Hessian of `h` is
`∇²h(x) = ∇²g(x) + β (J_c(x)J_c(x)ᵀ + Σᵢ cᵢ(x) ∇²cᵢ(x))` (3.10).

Under the blanket Assumptions 1.1 and 1.2 (`h11`, `h12`).

**Formalization Note** The Hessian of a function `φ` at `x` is `fderiv ℝ (gradient φ) x`.
Assumption 2.11 is the three hypotheses `Differentiable ℝ (fderiv ℝ ·)` for `f`, `c`, `A`.
The paper writes the second terms as `D_{J_A}(x)[∇f(A(x))]` and `D_{J_c}(x)[c(x)]`; read literally
(directional derivative of `J_A` along `∇f(A(x))`, p.5), (3.9) is false: for `n = 2`, `p = 1`,
`c(x) = x₂`, `A(x) = (x₁ + x₂², x₂²)`, `f(y) = y₁` one has `∇²g = diag(0, 2)` while the literal
right-hand side is `0`. The terms are stated here as the matrices `Σₖ vₖ∇²Aₖ(x)` (with
`v = ∇f(A(x))`) and `Σᵢ cᵢ(x)∇²cᵢ(x)`, which the chain rule gives. -/
theorem proposition_3_8 {n p : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin p)}
    {A : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (h11 : Assumption11 f c) (h12 : Assumption12 c A) :
    (∀ (β : ℝ) (x : EuclideanSpace ℝ (Fin n)),
        gradient (cdf f c A β) x = transJac A x (gradient f (A x)) + β • transJac c x (c x)) ∧
      (Differentiable ℝ (fderiv ℝ f) → Differentiable ℝ (fderiv ℝ c) →
        Differentiable ℝ (fderiv ℝ A) →
        ∀ (β : ℝ) (x : EuclideanSpace ℝ (Fin n)),
          fderiv ℝ (gradient (fun y => f (A y))) x =
              transJac A x ∘L fderiv ℝ (gradient f) (A x) ∘L
                  ContinuousLinearMap.adjoint (transJac A x) +
                (∑ k : Fin n, gradient f (A x) k • fderiv ℝ (gradient (fun y => A y k)) x) ∧
            fderiv ℝ (gradient (cdf f c A β)) x =
              fderiv ℝ (gradient (fun y => f (A y))) x +
                β • (transJac c x ∘L ContinuousLinearMap.adjoint (transJac c x) +
                  ∑ i : Fin p, c x i • fderiv ℝ (gradient (fun y => c y i)) x)) := by sorry

end DissolveCDF
