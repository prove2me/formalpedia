-- Prove2me | Theorems.Thm_BeckTeboulleMD_EMDA_bregman_ge_sq
-- name    : BeckTeboulleMD.EMDA.bregman_ge_sq
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T05:53:43.36893+00:00
-- url     : https://prove2.me/theorems/f3f6d117-60d2-41c0-8c03-adc3636a7530
-- title:
--   Proof of Theorem 4.1, p. 172 — B_ψ(·,·) is σ-strongly convex: B_ψ(u, y) ≥ 2⁻¹σ‖u − y‖²
-- statement:
--   Let $E$ be a real normed space, $X \subseteq E$, and $\psi : E \to \mathbb R$ strongly convex on $X$ with parameter $\sigma > 0$, i.e.
--   $$\psi(a u + b y) \le a\psi(u) + b\psi(y) - \tfrac{\sigma}{2}\, a b\, \|u - y\|^2$$
--   for $u, y \in X$ and $a, b \ge 0$ with $a + b = 1$. Then for all $u, y \in X$ such that $\psi$ is differentiable at $y$,
--   $$B_\psi(u, y) \ge \tfrac{\sigma}{2}\|u - y\|^2.$$
--
--   In the proof of Theorem 4.1 this is used in the form $-B_\psi(x^{k+1}, x^k) + 2^{-1}\sigma\|x^k - x^{k+1}\|^2 \le 0$, and it also gives $B_\psi \ge 0$.
--
--   **Formalization Note** Strong convexity is Mathlib's `StrongConvexOn X σ ψ`, the inequality displayed above. The page assumes $\psi$ continuously differentiable on $\operatorname{int} X$; here only differentiability at the second argument $y$ is assumed, which is what the inequality needs.
-- source:
--   Beck & Teboulle, Mirror descent and nonlinear projected subgradient methods for convex optimization, Oper. Res. Lett. 31 (2003), p. 172, proof of Theorem 4.1, the line before (4.21); σ introduced p. 169

import Mathlib
import Definitions.Def_BeckTeboulleMD_EMDA_Setting

namespace BeckTeboulleMD.EMDA

/-- Proof of Theorem 4.1, p. 172: if `ψ` is strongly convex on `X` with parameter `σ > 0`, then
`B_ψ(u, y) ≥ 2⁻¹ σ ‖u − y‖²` for all `u, y ∈ X` with `ψ` differentiable at `y`. -/
theorem bregman_ge_sq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X : Set E) (ψ : E → ℝ) (σ : ℝ) (hσ : 0 < σ) (hψ : StrongConvexOn X σ ψ) :
    ∀ u ∈ X, ∀ y ∈ X, DifferentiableAt ℝ ψ y → σ / 2 * ‖u - y‖ ^ 2 ≤ bregman ψ u y := by sorry

end BeckTeboulleMD.EMDA
