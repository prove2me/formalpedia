-- Prove2me | Theorems.Thm_AdaptiveCubic_FirstOrder_theorem_2_2
-- name    : AdaptiveCubic.FirstOrder.theorem_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:38:28.171476+00:00
-- url     : https://prove2.me/theorems/dcc2ea08-6f57-4006-b70e-86a6222296b7
-- title:
--   Theorem 2.2 — model decrease αε^p caps the successful iterations at ⌈κ_p ε^(−p)⌉
-- statement:
--   Consider a run of ARC (Algorithm 2.1) in which $m_k(s_k)<f(x_k)$ for every $k$ (2.6) and $f(x_k)\ge f_{\rm low}$ for every $k$. Let $\epsilon>0$, let $F_k\ge0$ be any measure of optimality, and let $\mathcal S_o$ be a set of successful iterations with $F_k>\epsilon$ (so $\mathcal S_o\subseteq\mathcal S^\epsilon_F$, (2.16)–(2.17)). Suppose there are constants $\alpha>0$ and $p>0$ with
--
--   $$f(x_k)-m_k(s_k)\ge\alpha\,\epsilon^p\quad\text{for all }k\in\mathcal S_o.$$
--
--   Then $\mathcal S_o$ is finite and
--
--   $$|\mathcal S_o|\le\left\lceil\kappa_p\,\epsilon^{-p}\right\rceil,\qquad \kappa_p=\frac{f(x_0)-f_{\rm low}}{\eta_1\alpha}.$$
--
--   Each successful iteration lowers $f$ by at least $\eta_1$ times the predicted decrease, so a uniform lower bound on the predicted decrease turns the total available decrease $f(x_0)-f_{\rm low}$ into a bound on the number of such iterations.
--
--   **Formalization Note** $\mathcal S_o$ is an arbitrary, possibly infinite, set of naturals; the theorem concludes that it is finite and bounds its cardinality. The standing assumption (2.6) (p. 4, and for ARC(S) p. 12) is an explicit hypothesis; it makes $\rho_k$ well defined and the values $f(x_k)$ nonincreasing. The exponent $p$ is real.
-- source:
--   Cartis, Gould & Toint, Adaptive cubic regularisation methods for unconstrained optimization. Part II, preprint rev. 15 Sep 2009 (UNamur), p. 6, Theorem 2.2, (2.16)–(2.19)

import Mathlib
import Definitions.Def_AdaptiveCubic_Cauchy_IsARCRun

open scoped RealInnerProductSpace

namespace AdaptiveCubic.FirstOrder

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

end AdaptiveCubic.FirstOrder
