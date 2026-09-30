-- Prove2me | Theorems.Thm_ChenWhitt93_Reflection_remark_2_2_tandem
-- name    : ChenWhitt93.Reflection.remark_2_2_tandem
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T23:45:35.473739+00:00
-- url     : https://prove2.me/theorems/cdcc80c2-b4c1-421c-a4d2-0f06cf84f085
-- title:
--   Remark (2.2) — two queues in series: Proposition 2.3 gives modulus $2$, Proposition 2.1 at best $4$
-- statement:
--   Consider $n = 2$ and
--   $$
--   Q = \begin{pmatrix} 0 & 0 \\ 1 & 0 \end{pmatrix},
--   $$
--   the routing of two queues in series. Then:
--
--   1. $Q$ satisfies the standing assumptions ($Q^{\mathsf t}$ substochastic, $Q^k \to 0$);
--   2. for $\Lambda = \mathrm{diag}(a,b)$ with $0 < a < b$, one has $\alpha = \|\Lambda^{-1}Q\Lambda\| = a/b$, and the modulus of (2.7) is $\|\Lambda\|\,\|\Lambda^{-1}\|/(1-\alpha) = 1/(z(1-z))$ with $z = a/b$, which is at least $4$;
--   3. every modulus $M \ge 4$ is obtained this way for some $0 < a < b$, and the modulus $4$ is obtained at $z = 1/2$ (for instance $\Lambda = \mathrm{diag}(1,2)$);
--   4. $\gamma = \|Q^2\| = 0$, and for all $T$, all $x_1, x_2 \in D([0,T],\mathbb R^2)$ and their reflections,
--   $$
--   \|\psi(x_1) - \psi(x_2)\| \le 2\,\|x_1 - x_2\| .
--   $$
--
--   So Proposition 2.3 can improve on Proposition 2.1 by a factor of two.
--
--   **Formalization Note** The norm on paths is $\|x\| = \sum_{j=1}^n \sup_{0\le t\le T}|x_j(t)|$ (the $\ell^1$ norm of the vector $|x|$ of coordinatewise sup norms). The printed (2.6) reads $\sup_{0\le t\le T}\sum_j |x_j(t)|$; under that norm the Lipschitz bounds of Propositions 2.1 and 2.3 fail for $n \ge 2$ (with $Q = 0$, $n = 2$, $T=1$, $x_1 \equiv 0$, $x_2 = (-1_{[0.1,0.2)}, -1_{[0.3,0.4)})$ one has $\|x_1 - x_2\| = 1$ but $\|\psi(x_1)-\psi(x_2)\| = 2$), whereas every step of the paper's proofs is valid for the sum-of-sups norm.
-- source:
--   Chen and Whitt, Diffusion approximations for open queueing networks with service interruptions, Queueing Systems 13 (1993), p. 341, Remark (2.2)

import Mathlib
import Definitions.Def_ChenWhitt93_Reflection_Basic
import Definitions.Def_ChenWhitt93_Reflection_ReflectionMap

open Filter Topology Matrix

namespace ChenWhitt93.Reflection

/-- Remark (2.2) (p. 341): for the tandem network `n = 2`, `Q = !![0, 0; 1, 0]`, the standing
assumptions hold; with `Λ = diag(a, b)`, `0 < a < b`, Proposition 2.1 has `α = a/b` and
modulus `‖Λ‖‖Λ⁻¹‖/(1 − α) = 1/(z(1 − z))`, `z = a/b`, which is at least `4`; every
modulus `M ≥ 4` is obtained for some such `Λ`, and `4` is obtained at `z = 1/2` (`Λ = diag(1, 2)`); while
`γ = ‖Q²‖ = 0` and (2.10) of Proposition 2.3 gives `‖ψ(x₁) − ψ(x₂)‖ ≤ 2‖x₁ − x₂‖`. -/
theorem remark_2_2_tandem :
    let Q : Matrix (Fin 2) (Fin 2) ℝ := !![0, 0; 1, 0]
    IsTransientSubstochasticT Q ∧
    (∀ a b : ℝ, 0 < a → a < b →
      colNorm ((diagonal ![a, b])⁻¹ * Q * diagonal ![a, b]) = a / b ∧
      colNorm (diagonal ![a, b]) * colNorm (diagonal ![a, b])⁻¹ / (1 - a / b)
        = 1 / (a / b * (1 - a / b)) ∧
      4 ≤ 1 / (a / b * (1 - a / b))) ∧
    (∀ M : ℝ, 4 ≤ M → ∃ a b : ℝ, 0 < a ∧ a < b ∧
      colNorm (diagonal ![a, b]) * colNorm (diagonal ![a, b])⁻¹ / (1 - a / b) = M) ∧
    colNorm (diagonal ![(1 : ℝ), 2]) * colNorm (diagonal ![(1 : ℝ), 2])⁻¹ / (1 - 1 / 2) = 4 ∧
    colNorm (Q ^ 2) = 0 ∧
    ∀ (T : ℝ) (x₁ x₂ y₁ z₁ y₂ z₂ : ℝ → Fin 2 → ℝ),
      IsCadlagOn T x₁ → IsCadlagOn T x₂ →
      IsReflection Q T x₁ y₁ z₁ → IsReflection Q T x₂ y₂ z₂ →
      sumSupNorm T (y₁ - y₂) ≤ 2 * sumSupNorm T (x₁ - x₂) := by sorry

end ChenWhitt93.Reflection
