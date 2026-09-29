-- Prove2me | Theorems.Thm_CubicNewton_GradDom_delta_recursion
-- name    : CubicNewton.GradDom.delta_recursion
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T21:30:45.060372+00:00
-- url     : https://prove2.me/theorems/b47f4c81-d64c-434a-b7ca-e9a44c66c6f7
-- title:
--   Eq. (4.17) — $\delta_k \ge \delta_{k+1} + \delta_{k+1}^{3/4}$ for gradient dominated $f$ of degree 2
-- statement:
--   Assume the standing assumptions (closed convex $F$, $L$-Lipschitz Hessian with $L > 0$, $x_0 \in \operatorname{int} F$ with $\{x : f(x) \le f(x_0)\} \subseteq \operatorname{int} F$), and let $f$ be gradient dominated of degree $2$ on $F$ with constant $\tau_f > 0$ and global minimizer $x^*$. Let $0 < L_0 \le L$, let $(x_k, M_k)_{k\ge0}$ be any run of method (3.3) from $x_0$, and put
--   $$\tilde\omega = \frac{L_0^4}{324 (L + L_0)^6 \tau_f^3}, \qquad \delta_k = \frac{f(x_k) - f(x^*)}{\tilde\omega} .$$
--   Then for every $k \ge 0$
--   $$\delta_k \ge \delta_{k+1} + \delta_{k+1}^{3/4} .$$
--   This scalar recursion is the whole content of the method's behaviour on this class; both phases of Theorem 7 are read off from it.
--
--   **Formalization Note** $\delta_{k+1} \ge 0$ because $x^*$ minimizes $f$ on $F$ and the iterates stay in $F$; the power is `Real.rpow`.
-- source:
--   Nesterov & Polyak, Cubic regularization of Newton method and its global performance, Math. Program. Ser. A 108 (2006) 177–205, DOI 10.1007/s10107-006-0706-8, p. 195, Section 4.2, Eq. (4.17) (proof of Theorem 7)

import Mathlib
import Definitions.Def_CubicNewton_Shared_IsCubicNewtonRun
import Definitions.Def_CubicNewton_GradDom_IsGradDominated2
import Definitions.Def_CubicNewton_GradDom_omegaTilde

open scoped RealInnerProductSpace

namespace CubicNewton.GradDom

/-- Nesterov–Polyak 2006, Section 4.2, Eq. (4.17), p. 195 (proof of Theorem 7): for a gradient
dominated `f` of degree 2 and every run of method (3.3), with `ω̃ = L₀⁴ / (324 (L + L₀)⁶ τ_f³)` and
`δ_k = (f(x_k) − f(x*))/ω̃`, one has `δ_k ≥ δ_{k+1} + δ_{k+1}^{3/4}` for every `k ≥ 0`. -/
theorem delta_recursion {n : ℕ}
    (F : Set (EuclideanSpace ℝ (Fin n))) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (L : ℝ)
    (hF_closed : IsClosed F) (hF_convex : Convex ℝ F)
    (hf : ∀ x ∈ F, HasGradientAt f (g x) x) (hg : ∀ x ∈ F, HasFDerivAt g (H x) x)
    (hL : 0 < L) (hLip : ∀ x ∈ F, ∀ y ∈ F, ‖H x - H y‖ ≤ L * ‖x - y‖)
    (x₀ : EuclideanSpace ℝ (Fin n)) (hx₀ : x₀ ∈ interior F)
    (hlevel : {x | f x ≤ f x₀} ⊆ interior F)
    (τ : ℝ) (xs : EuclideanSpace ℝ (Fin n)) (hdom : IsGradDominated2 F f g τ xs)
    (L₀ : ℝ) (hL₀ : 0 < L₀) (hL₀L : L₀ ≤ L)
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (M : ℕ → ℝ) (hrun : CubicNewton.Shared.IsCubicNewtonRun f g H L₀ L x₀ x M) :
    ∀ k : ℕ, (f (x k) - f xs) / omegaTilde L₀ L τ ≥
      (f (x (k + 1)) - f xs) / omegaTilde L₀ L τ +
        ((f (x (k + 1)) - f xs) / omegaTilde L₀ L τ) ^ (3 / 4 : ℝ) := by sorry

end CubicNewton.GradDom
