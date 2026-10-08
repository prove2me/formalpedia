-- Prove2me | Theorems.Thm_BeckTeboulleMD_EMDA_one_step_4_21
-- name    : BeckTeboulleMD.EMDA.one_step_4_21
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T05:53:53.181745+00:00
-- url     : https://prove2.me/theorems/d0fe45f7-2325-4aa4-abfe-9d42cdb03e1c
-- title:
--   (4.21), p. 172 — t_k(f(x^k) − f(x*)) ≤ B_ψ(x*,x^k) − B_ψ(x*,x^{k+1}) + (2σ)⁻¹t_k²‖f′(x^k)‖²_*
-- statement:
--   Let $E$ be a real normed space and $X \subseteq E$ convex. Let $f : E \to \mathbb R$ be convex on $X$ with a minimiser $x^* \in X$, and let $f'$ be a subgradient oracle on $X$: $f(x) + \langle y - x, f'(x)\rangle \le f(y)$ for all $x, y \in X$. Let $\psi$ be strongly convex on $X$ with parameter $\sigma > 0$ and let $(x^k)_{k \ge 1}$ be a SANP run over $X$ with step sizes $t_k$. Then for every $k \ge 1$,
--   $$t_k\big(f(x^k) - f(x^*)\big) \le B_\psi(x^*, x^k) - B_\psi(x^*, x^{k+1}) + (2\sigma)^{-1} t_k^2 \|f'(x^k)\|_*^2. \tag{4.21}$$
--
--   Summed over $k$, this one-step inequality telescopes into the efficiency estimate (4.22) of Theorem 4.1.
--
--   **Formalization Note** $\|f'(x^k)\|_*$ is the operator norm of the functional $f'(x^k)$, which is the paper's dual norm $\max\{\langle x, z\rangle : \|x\| \le 1\}$. The page writes "$= s_1 + s_2 + s_3 \le$"; only the resulting inequality is stated. Closedness of $X$ and the Lipschitz constant of Assumption A are not needed and are omitted; the run replaces "nonempty interior" and "$x^1 \in \operatorname{int} X$" (see the definitions file).
-- source:
--   Beck & Teboulle, Mirror descent and nonlinear projected subgradient methods for convex optimization, Oper. Res. Lett. 31 (2003), p. 172, proof of Theorem 4.1, (4.21)

import Mathlib
import Definitions.Def_BeckTeboulleMD_EMDA_Setting

namespace BeckTeboulleMD.EMDA

/-- Proof of Theorem 4.1, (4.21), p. 172: for a SANP run under Assumption A, for every `k ≥ 1`,
`t_k (f(x^k) − f(x*)) ≤ B_ψ(x*, x^k) − B_ψ(x*, x^{k+1}) + (2σ)⁻¹ t_k² ‖f′(x^k)‖²_*`. -/
theorem one_step_4_21 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X : Set E) (hXconv : Convex ℝ X)
    (f : E → ℝ) (hf : ConvexOn ℝ X f)
    (xstar : E) (hxstar : xstar ∈ X) (hmin : ∀ y ∈ X, f xstar ≤ f y)
    (g : E → E →L[ℝ] ℝ) (hg : ∀ x ∈ X, ∀ y ∈ X, f x + g x (y - x) ≤ f y)
    (ψ : E → ℝ) (σ : ℝ) (hσ : 0 < σ) (hψ : StrongConvexOn X σ ψ)
    (t : ℕ → ℝ) (x : ℕ → E) (hrun : IsSANPRun X ψ g t x) :
    ∀ k, 1 ≤ k → t k * (f (x k) - f xstar)
      ≤ bregman ψ xstar (x k) - bregman ψ xstar (x (k + 1))
        + 1 / (2 * σ) * t k ^ 2 * ‖g (x k)‖ ^ 2 := by sorry

end BeckTeboulleMD.EMDA
