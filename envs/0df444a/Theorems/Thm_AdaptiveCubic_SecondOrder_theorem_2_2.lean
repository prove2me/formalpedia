-- Prove2me | Theorems.Thm_AdaptiveCubic_SecondOrder_theorem_2_2
-- name    : AdaptiveCubic.SecondOrder.theorem_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:38:25.537377+00:00
-- url     : https://prove2.me/theorems/c9c37c8c-a8c8-4581-b135-9240827671b1
-- title:
--   Theorem 2.2 — a model decrease of αε^p caps the number of successful iterations
-- statement:
--   Consider a run of the ARC algorithm with $m_k(s_k)<f(x_k)$ for all $k$ (2.6) and $f(x_k)\ge f_{\rm low}$ for all $k$. Let $\epsilon>0$, let $F_k\ge0$ be a measure of optimality, $\mathcal S^\epsilon_F=\{k\in\mathcal S: F_k>\epsilon\}$ (2.16), and let $\mathcal S_o\subseteq\mathcal S^\epsilon_F$ (2.17). Suppose that
--
--   $$f(x_k)-m_k(s_k)\ge\alpha\epsilon^p \quad\text{for all } k\in\mathcal S_o, \qquad (2.18)$$
--
--   with constants $\alpha>0$ and $p>0$. Then $\mathcal S_o$ is finite and
--
--   $$|\mathcal S_o| \le \left\lceil \kappa_p\,\epsilon^{-p}\right\rceil, \qquad \kappa_p=\frac{f(x_0)-f_{\rm low}}{\eta_1\alpha}.$$
--
--   Each successful iteration in $\mathcal S_o$ lowers $f$ by at least $\eta_1\alpha\epsilon^p$, and $f$ never increases, so the total decrease available, $f(x_0)-f_{\rm low}$, limits their number. Every complexity bound of the paper on successful iterations is an instance.
--
--   **Formalization Note** The standing assumption (2.6) of p. 4 is an explicit hypothesis for every $k$.
-- source:
--   Cartis, Gould & Toint, Adaptive cubic regularisation methods for unconstrained optimization. Part II, preprint rev. 15 Sep 2009 (UNamur), p. 6, Theorem 2.2

import Mathlib
import Definitions.Def_AdaptiveCubic_Cauchy_IsARCRun

open scoped RealInnerProductSpace

namespace AdaptiveCubic.SecondOrder

/-- Theorem 2.2, p. 6 (Cartis, Gould & Toint, ARC Part II, preprint rev. 15 Sep 2009).
Let `f(x_k) ≥ f_low` for all `k`, `ε > 0`, `F_k ≥ 0` a measure of optimality,
`S^ε_F = {k ∈ S : F_k > ε}` (2.16) and `S_o ⊆ S^ε_F` (2.17). If
`f(x_k) − m_k(s_k) ≥ α ε^p` for all `k ∈ S_o` (2.18), with `α > 0` and `p > 0`, then `S_o` is
finite and `|S_o| ≤ ⌈κ_p ε^{−p}⌉` (2.19), where `κ_p = (f(x₀) − f_low)/(η₁ α)`.
The standing assumption (2.6), `m_k(s_k) < f(x_k)` for all `k` (p. 4), is a hypothesis. -/
theorem theorem_2_2 {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (γ₁ γ₂ η₁ η₂ : ℝ)
    (x s : ℕ → EuclideanSpace ℝ (Fin n)) (σ : ℕ → ℝ)
    (B : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hrun : AdaptiveCubic.Cauchy.IsARCRun f γ₁ γ₂ η₁ η₂ x s σ B)
    (h26 : ∀ k, AdaptiveCubic.Cauchy.model f (B k) (σ k) (x k) (s k) < f (x k))
    (flow : ℝ) (hflow : ∀ k, flow ≤ f (x k))
    (ε : ℝ) (hε : 0 < ε) (F : ℕ → ℝ) (hF : ∀ k, 0 ≤ F k)
    (So : Set ℕ) (hSo : So ⊆ {k | η₁ ≤ AdaptiveCubic.Cauchy.rho f (B k) (σ k) (x k) (s k) ∧ ε < F k})
    (α p : ℝ) (hα : 0 < α) (hp : 0 < p)
    (h218 : ∀ k ∈ So, α * ε ^ p ≤ f (x k) - AdaptiveCubic.Cauchy.model f (B k) (σ k) (x k) (s k)) :
    So.Finite ∧ (So.ncard : ℤ) ≤ ⌈(f (x 0) - flow) / (η₁ * α) * ε ^ (-p)⌉ := by sorry

end AdaptiveCubic.SecondOrder
