-- Prove2me | Theorems.Thm_ChenWhitt93_Reflection_proposition_2_2_contraction
-- name    : ChenWhitt93.Reflection.proposition_2_2_contraction
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T23:28:56.996618+00:00
-- url     : https://prove2.me/theorems/bd60ec10-cb50-4d6e-ac58-f963f1916dff
-- title:
--   Proposition 2.2 — $\pi_x$ is an $n$-stage contraction and $\pi_x^k(y_1) \to \psi(x)$
-- statement:
--   Let $Q$ be an $n\times n$ matrix with $Q^{\mathsf t}$ substochastic and $Q^k \to 0$, let $\gamma = \|Q^n\|$ in the norm (2.5), let $T \in \mathbb R$ and $x \in D([0,T],\mathbb R^n)$, and let $\pi_x(y) = (Qy - x)^{\uparrow}\vee 0$ be the operator of (2.4), with $k$-fold iterate $\pi_x^k$. For any $y_1, y_2 \in D([0,T],\mathbb R^n)$:
--
--   1. for all $k \ge 1$,
--   $$
--   \|\pi_x^k(y_1) - \pi_x^k(y_2)\| \le \big\|Q^k\,|y_1 - y_2|\big\| \le \|y_1 - y_2\| ;
--   $$
--   2. for all $k \ge n$,
--   $$
--   \|\pi_x^k(y_1) - \pi_x^k(y_2)\| \le \gamma\,\|y_1 - y_2\| ;
--   $$
--   3. consequently $\pi_x^k(y_1) \to \psi(x)$ as $k \to \infty$: for every reflection $(y,z) = (\psi(x),\phi(x))$ of $x$, $\|\pi_x^k(y_1) - y\| \to 0$.
--
--   Here $|y_1 - y_2| \in \mathbb R^n$ is the vector of coordinatewise sup norms on $[0,T]$ and $\|c\| = \sum_j |c_j|$ for vectors.
--
--   This is the paper's route to uniqueness of $\psi(x)$ and to the convergence $\pi_x^k(0) \to \psi(x)$ used in the proof of Proposition 2.3.
--
--   **Formalization Note** The norm on paths is $\|x\| = \sum_{j=1}^n \sup_{0\le t\le T}|x_j(t)|$ (the $\ell^1$ norm of the vector $|x|$ of coordinatewise sup norms). The printed (2.6) reads $\sup_{0\le t\le T}\sum_j |x_j(t)|$; under that norm the Lipschitz bounds of Propositions 2.1 and 2.3 fail for $n \ge 2$ (with $Q = 0$, $n = 2$, $T=1$, $x_1 \equiv 0$, $x_2 = (-1_{[0.1,0.2)}, -1_{[0.3,0.4)})$ one has $\|x_1 - x_2\| = 1$ but $\|\psi(x_1)-\psi(x_2)\| = 2$), whereas every step of the paper's proofs is valid for the sum-of-sups norm. Iterates are `Nat.iterate`. Clause 3 is stated for every solution pair $(y,z)$ of (2.1)–(2.3), so it is informative exactly when $x(0) \ge 0$ (see the existence item).
-- source:
--   Chen and Whitt, Diffusion approximations for open queueing networks with service interruptions, Queueing Systems 13 (1993), p. 339, Proposition 2.2

import Mathlib
import Definitions.Def_ChenWhitt93_Reflection_Basic
import Definitions.Def_ChenWhitt93_Reflection_ReflectionMap

open Filter Topology Matrix

namespace ChenWhitt93.Reflection

/-- Proposition 2.2 (p. 339): with `γ = ‖Qⁿ‖`, for all `y₁, y₂ ∈ D`,
`‖πₓᵏ(y₁) − πₓᵏ(y₂)‖ ≤ ‖Qᵏ|y₁ − y₂|‖ ≤ ‖y₁ − y₂‖` for `k ≥ 1`,
`‖πₓᵏ(y₁) − πₓᵏ(y₂)‖ ≤ γ‖y₁ − y₂‖` for `k ≥ n`, and `πₓᵏ(y₁) → ψ(x)`.
The norm on `D` is `sumSupNorm` (see the definition file). -/
theorem proposition_2_2_contraction {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℝ)
    (hQ : IsTransientSubstochasticT Q) (T : ℝ) (x y₁ y₂ : ℝ → Fin n → ℝ)
    (hx : IsCadlagOn T x) (hy₁ : IsCadlagOn T y₁) (hy₂ : IsCadlagOn T y₂) :
    (∀ k : ℕ, 1 ≤ k →
      sumSupNorm T ((piMap Q x)^[k] y₁ - (piMap Q x)^[k] y₂)
          ≤ l1 ((Q ^ k) *ᵥ supVec T (y₁ - y₂)) ∧
        l1 ((Q ^ k) *ᵥ supVec T (y₁ - y₂)) ≤ sumSupNorm T (y₁ - y₂)) ∧
    (∀ k : ℕ, n ≤ k →
      sumSupNorm T ((piMap Q x)^[k] y₁ - (piMap Q x)^[k] y₂)
          ≤ colNorm (Q ^ n) * sumSupNorm T (y₁ - y₂)) ∧
    (∀ y z : ℝ → Fin n → ℝ, IsReflection Q T x y z →
      Tendsto (fun k : ℕ => sumSupNorm T ((piMap Q x)^[k] y₁ - y)) atTop (𝓝 0)) := by sorry

end ChenWhitt93.Reflection
