-- Prove2me | Theorems.Thm_ChenWhitt93_Reflection_proposition_2_1_lipschitz
-- name    : ChenWhitt93.Reflection.proposition_2_1_lipschitz
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T23:34:32.796028+00:00
-- url     : https://prove2.me/theorems/af7fa833-b4d6-42cc-af59-2749965b5156
-- title:
--   Proposition 2.1 — Lipschitz bounds (2.7)–(2.8) via a diagonal similarity $Q^* = \Lambda^{-1}Q\Lambda$
-- statement:
--   Let $Q$ be an $n\times n$ matrix with $Q^{\mathsf t}$ substochastic and $Q^k \to 0$. Let $\Lambda$ be an invertible diagonal matrix and $Q^* = \Lambda^{-1} Q \Lambda$ with $\|Q^*\| = \alpha < 1$ in the norm (2.5). For any $x_1, x_2 \in D([0,T],\mathbb R^n)$ and reflections $(\psi(x_i),\phi(x_i))$ of $x_i$,
--   $$
--   \|\psi(x_1) - \psi(x_2)\| \le \frac{\|\Lambda\|\,\|\Lambda^{-1}\|}{1-\alpha}\,\|x_1 - x_2\| \tag{2.7}
--   $$
--   and
--   $$
--   \|\phi(x_1) - \phi(x_2)\| \le \Big(1 + \frac{\|I - Q\|\,\|\Lambda\|\,\|\Lambda^{-1}\|}{1-\alpha}\Big)\|x_1 - x_2\| . \tag{2.8}
--   $$
--
--   This is the paper's Lipschitz bound in the Harrison–Reiman scaling; Proposition 2.3 gives a bound that does not require choosing $\Lambda$.
--
--   **Formalization Note** The page prints the left side of (2.8) as $\|\phi(x_1) - \phi(x_1)\|$, a typo for $\phi(x_1) - \phi(x_2)$, which is stated here. The page says only "$\Lambda$ is diagonal"; $\Lambda = \mathrm{diag}(d)$ with every $d_i \neq 0$ (needed for $\Lambda^{-1}$). All quantities depend on $\Lambda$ only through $|d_i|$, so this covers the positive diagonal Harrison and Reiman use. The norm on paths is $\|x\| = \sum_{j=1}^n \sup_{0\le t\le T}|x_j(t)|$ (the $\ell^1$ norm of the vector $|x|$ of coordinatewise sup norms). The printed (2.6) reads $\sup_{0\le t\le T}\sum_j |x_j(t)|$; under that norm the Lipschitz bounds of Propositions 2.1 and 2.3 fail for $n \ge 2$ (with $Q = 0$, $n = 2$, $T=1$, $x_1 \equiv 0$, $x_2 = (-1_{[0.1,0.2)}, -1_{[0.3,0.4)})$ one has $\|x_1 - x_2\| = 1$ but $\|\psi(x_1)-\psi(x_2)\| = 2$), whereas every step of the paper's proofs is valid for the sum-of-sups norm. Paths are functions $\mathbb R \to \mathbb R^n$ of which only the restriction to $[0,T]$ matters; $x \in D([0,T],\mathbb R^n)$ is the predicate `IsCadlagOn`. A pair $(y,z)$ with `IsReflection Q T x y z` is exactly a pair $(\psi(x),\phi(x))$; the theorem is stated for every such pair, so no choice of the map is involved.
-- source:
--   Chen and Whitt, Diffusion approximations for open queueing networks with service interruptions, Queueing Systems 13 (1993), p. 338, Proposition 2.1, Eqs. (2.7)–(2.8)

import Mathlib
import Definitions.Def_ChenWhitt93_Reflection_Basic
import Definitions.Def_ChenWhitt93_Reflection_ReflectionMap

open Filter Topology Matrix

namespace ChenWhitt93.Reflection

/-- Proposition 2.1 (p. 338): let `Q* = Λ⁻¹QΛ` with `Λ = diag(d)` diagonal (invertible) and
`‖Q*‖ = α < 1`. Then for any `x₁, x₂ ∈ D` and their reflections `(yᵢ, zᵢ) = (ψ(xᵢ), φ(xᵢ))`,
(2.7) `‖ψ(x₁) − ψ(x₂)‖ ≤ ‖Λ‖‖Λ⁻¹‖/(1 − α) · ‖x₁ − x₂‖` and
(2.8) `‖φ(x₁) − φ(x₂)‖ ≤ (1 + ‖I − Q‖‖Λ‖‖Λ⁻¹‖/(1 − α)) ‖x₁ − x₂‖`
(the printed (2.8) reads `φ(x₁) − φ(x₁)`). -/
theorem proposition_2_1_lipschitz {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℝ)
    (hQ : IsTransientSubstochasticT Q) (d : Fin n → ℝ) (hd : ∀ i, d i ≠ 0) (α : ℝ)
    (hα : colNorm ((diagonal d)⁻¹ * Q * diagonal d) = α) (hα1 : α < 1)
    (T : ℝ) (x₁ x₂ y₁ z₁ y₂ z₂ : ℝ → Fin n → ℝ)
    (hx₁ : IsCadlagOn T x₁) (hx₂ : IsCadlagOn T x₂)
    (h₁ : IsReflection Q T x₁ y₁ z₁) (h₂ : IsReflection Q T x₂ y₂ z₂) :
    sumSupNorm T (y₁ - y₂)
        ≤ colNorm (diagonal d) * colNorm (diagonal d)⁻¹ / (1 - α) * sumSupNorm T (x₁ - x₂) ∧
    sumSupNorm T (z₁ - z₂)
        ≤ (1 + colNorm (1 - Q) * colNorm (diagonal d) * colNorm (diagonal d)⁻¹ / (1 - α))
            * sumSupNorm T (x₁ - x₂) := by sorry

end ChenWhitt93.Reflection
