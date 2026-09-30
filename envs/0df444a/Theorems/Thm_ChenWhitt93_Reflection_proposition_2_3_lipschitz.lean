-- Prove2me | Theorems.Thm_ChenWhitt93_Reflection_proposition_2_3_lipschitz
-- name    : ChenWhitt93.Reflection.proposition_2_3_lipschitz
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T23:40:14.224044+00:00
-- url     : https://prove2.me/theorems/109e56b9-e515-46c6-8725-c1f1c7be892a
-- title:
--   Proposition 2.3 — explicit Lipschitz bounds (2.9)–(2.11) for the reflection map
-- statement:
--   Let $Q$ be an $n\times n$ matrix whose transpose is substochastic and with $Q^k \to 0$ as $k\to\infty$, and let $\gamma = \|Q^n\|$ in the maximum-column-sum norm (2.5). For any $x_1, x_2 \in D([0,T],\mathbb R^n)$ with reflections $(\psi(x_i),\phi(x_i))$:
--
--   1. componentwise in $\mathbb R^n$,
--   $$
--   |\psi(x_1) - \psi(x_2)| \le (I - Q)^{-1}\,|x_1 - x_2| ; \tag{2.9}
--   $$
--   2. the series $\sum_{k\ge0}\|Q^k\|$ converges and
--   $$
--   \|\psi(x_1) - \psi(x_2)\| \le \|(I - Q)^{-1}\|\,\|x_1 - x_2\| \le \sum_{k=0}^{\infty}\|Q^k\|\,\|x_1 - x_2\| \le \frac{n}{1-\gamma}\,\|x_1 - x_2\| ; \tag{2.10}
--   $$
--   3. and
--   $$
--   \|\phi(x_1) - \phi(x_2)\| \le \big(1 + \|I - Q\|\,\|(I-Q)^{-1}\|\big)\|x_1 - x_2\| \le \Big(1 + \frac{2n}{1-\gamma}\Big)\|x_1 - x_2\| . \tag{2.11}
--   $$
--
--   Here $|x|$ is the vector of coordinatewise sup norms of a path on $[0,T]$, $\|c\| = \sum_j|c_j|$ on vectors, and $\|x\| = \big\||x|\big\|$ on paths.
--
--   The result makes the reflection map, and hence the queue-content and idleness processes of an open network, Lipschitz in the uniform topology with a modulus computed from $Q$ alone; this is what transfers functional limit theorems for netput processes to the network.
--
--   **Formalization Note** The norm on paths is $\|x\| = \sum_{j=1}^n \sup_{0\le t\le T}|x_j(t)|$ (the $\ell^1$ norm of the vector $|x|$ of coordinatewise sup norms). The printed (2.6) reads $\sup_{0\le t\le T}\sum_j |x_j(t)|$; under that norm the Lipschitz bounds of Propositions 2.1 and 2.3 fail for $n \ge 2$ (with $Q = 0$, $n = 2$, $T=1$, $x_1 \equiv 0$, $x_2 = (-1_{[0.1,0.2)}, -1_{[0.3,0.4)})$ one has $\|x_1 - x_2\| = 1$ but $\|\psi(x_1)-\psi(x_2)\| = 2$), whereas every step of the paper's proofs is valid for the sum-of-sups norm. Under the standing assumptions $I - Q$ is invertible with nonnegative inverse $\sum_k Q^k$; `(1 - Q)⁻¹` is Mathlib's matrix inverse. The chains (2.10) and (2.11) are stated link by link, each multiplied by $\|x_1 - x_2\|$ exactly as printed, and the sum $\sum_k \|Q^k\|$ is a `tsum` accompanied by its summability. Paths are functions $\mathbb R \to \mathbb R^n$ of which only the restriction to $[0,T]$ matters; $x \in D([0,T],\mathbb R^n)$ is the predicate `IsCadlagOn`. A pair $(y,z)$ with `IsReflection Q T x y z` is exactly a pair $(\psi(x),\phi(x))$; the theorem is stated for every such pair, so no choice of the map is involved.
-- source:
--   Chen and Whitt, Diffusion approximations for open queueing networks with service interruptions, Queueing Systems 13 (1993), pp. 339–340, Proposition 2.3, Eqs. (2.9)–(2.11)

import Mathlib
import Definitions.Def_ChenWhitt93_Reflection_Basic
import Definitions.Def_ChenWhitt93_Reflection_ReflectionMap

open Filter Topology Matrix

namespace ChenWhitt93.Reflection

/-- Proposition 2.3 (pp. 339–340): for any `x₁, x₂ ∈ D` with reflections
`(yᵢ, zᵢ) = (ψ(xᵢ), φ(xᵢ))` and `γ = ‖Qⁿ‖`:
(2.9) `|ψ(x₁) − ψ(x₂)| ≤ (I − Q)⁻¹|x₁ − x₂|` componentwise;
(2.10) `‖ψ(x₁) − ψ(x₂)‖ ≤ ‖(I − Q)⁻¹‖‖x₁ − x₂‖ ≤ ∑ₖ ‖Qᵏ‖ ‖x₁ − x₂‖ ≤ n/(1 − γ) ‖x₁ − x₂‖`
(with `∑ₖ ‖Qᵏ‖` convergent);
(2.11) `‖φ(x₁) − φ(x₂)‖ ≤ (1 + ‖I − Q‖‖(I − Q)⁻¹‖)‖x₁ − x₂‖ ≤ (1 + 2n/(1 − γ))‖x₁ − x₂‖`. -/
theorem proposition_2_3_lipschitz {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℝ)
    (hQ : IsTransientSubstochasticT Q) (T : ℝ) (x₁ x₂ y₁ z₁ y₂ z₂ : ℝ → Fin n → ℝ)
    (hx₁ : IsCadlagOn T x₁) (hx₂ : IsCadlagOn T x₂)
    (h₁ : IsReflection Q T x₁ y₁ z₁) (h₂ : IsReflection Q T x₂ y₂ z₂) :
    -- (2.9)
    supVec T (y₁ - y₂) ≤ (1 - Q)⁻¹ *ᵥ supVec T (x₁ - x₂) ∧
    -- (2.10)
    sumSupNorm T (y₁ - y₂) ≤ colNorm (1 - Q)⁻¹ * sumSupNorm T (x₁ - x₂) ∧
    Summable (fun k : ℕ => colNorm (Q ^ k)) ∧
    colNorm (1 - Q)⁻¹ * sumSupNorm T (x₁ - x₂)
        ≤ (∑' k : ℕ, colNorm (Q ^ k)) * sumSupNorm T (x₁ - x₂) ∧
    (∑' k : ℕ, colNorm (Q ^ k)) * sumSupNorm T (x₁ - x₂)
        ≤ (n : ℝ) / (1 - colNorm (Q ^ n)) * sumSupNorm T (x₁ - x₂) ∧
    -- (2.11)
    sumSupNorm T (z₁ - z₂)
        ≤ (1 + colNorm (1 - Q) * colNorm (1 - Q)⁻¹) * sumSupNorm T (x₁ - x₂) ∧
    (1 + colNorm (1 - Q) * colNorm (1 - Q)⁻¹) * sumSupNorm T (x₁ - x₂)
        ≤ (1 + 2 * (n : ℝ) / (1 - colNorm (Q ^ n))) * sumSupNorm T (x₁ - x₂) := by sorry

end ChenWhitt93.Reflection
