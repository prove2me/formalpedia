-- Prove2me | Theorems.Thm_AdaptiveCubic_Cauchy_theorem_2_2
-- name    : AdaptiveCubic.Cauchy.theorem_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:43:31.672989+00:00
-- url     : https://prove2.me/theorems/7a4238ba-d85c-4841-b801-40ecac9f58f0
-- title:
--   Theorem 2.2 — at most $\lceil\kappa_p\epsilon^{-p}\rceil$ successful iterations decrease the model by $\alpha\epsilon^p$
-- statement:
--   Consider a run of the ARC algorithm with parameters $\gamma_2\ge\gamma_1>1$, $1>\eta_2\ge\eta_1>0$, $\sigma_0>0$, and suppose $f(x_k)\ge f_{\rm low}$ for all $k$. Let $\epsilon>0$, $\alpha>0$ and $p>0$. Fix a horizon $j$ such that the model decreases on every iteration up to it,
--
--   $$m_k(s_k)<f(x_k)\quad\text{for all }k\le j, \qquad (2.6)$$
--
--   and let $\mathcal S_o$ be any set of successful iterations $k\le j$ with
--
--   $$f(x_k)-m_k(s_k)\ge\alpha\epsilon^p\quad\text{for all }k\in\mathcal S_o. \qquad (2.18)$$
--
--   Then
--
--   $$
--   |\mathcal S_o|\le\left\lceil\kappa_p\,\epsilon^{-p}\right\rceil,\qquad \kappa_p=\frac{f(x_0)-f_{\rm low}}{\eta_1\alpha}.
--   $$
--
--   Each such iteration lowers $f$ by at least $\eta_1\alpha\epsilon^p$, and $f$ never increases along the run, so the total available decrease $f(x_0)-f_{\rm low}$ caps their number. This is the generic counting step behind every complexity bound of the paper.
--
--   **Formalization Note** The paper assumes (2.6) on every iteration (p. 4) and sums over all of $\mathcal S_o$ "with say $j_m\le\infty$ as the largest index". Here the statement is posed for each finite horizon $j$, with (2.6) assumed up to $j$; the infinite case follows by letting $j$ grow. The optimality measure $F_k\ge0$ and the set $\mathcal S^\epsilon_F=\{k\in\mathcal S: F_k>\epsilon\}$ of (2.16)–(2.17) only restrict which $\mathcal S_o$ are allowed; since $F_k$ is arbitrary, allowing every set of successful iterations is the same theorem.
-- source:
--   Cartis, Gould & Toint, Adaptive cubic regularisation methods for unconstrained optimization. Part II, preprint rev. 15 Sep 2009 (UNamur), p. 6, Theorem 2.2, (2.16)–(2.19)

import Mathlib
import Definitions.Def_AdaptiveCubic_Cauchy_IsARCRun

open scoped RealInnerProductSpace

namespace AdaptiveCubic.Cauchy

/-- Theorem 2.2, (2.19), p. 6 (Cartis, Gould & Toint, ARC Part II, preprint rev. 15 Sep 2009),
finite-horizon form. Let `f(x_k) ≥ f_low` for all `k`, `ϵ > 0`, `α > 0`, `p > 0`. Fix a horizon `j`
on which (2.6) `m_k(s_k) < f(x_k)` holds for every `k ≤ j`, and let `S_o` be any set of successful
iterations `k ≤ j` with (2.18) `f(x_k) − m_k(s_k) ≥ α ϵ^p` for `k ∈ S_o`. Then
`|S_o| ≤ ⌈κ_p ϵ^{−p}⌉` with `κ_p = (f(x_0) − f_low)/(η₁ α)`.

The paper assumes (2.6) on every iteration (p. 4, last paragraph); here it is assumed up to the
horizon, which is the "largest index `j_m`" of the page's proof. The optimality measure `F_k` and
`S^ϵ_F` of (2.16)–(2.17) only constrain which `S_o` are allowed; since `F_k ≥ 0` is arbitrary, the
statement for all successful `S_o` is the same theorem. -/
theorem theorem_2_2 {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (γ₁ γ₂ η₁ η₂ : ℝ)
    (x s : ℕ → EuclideanSpace ℝ (Fin n)) (σ : ℕ → ℝ)
    (B : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hrun : IsARCRun f γ₁ γ₂ η₁ η₂ x s σ B)
    (flow : ℝ) (hlow : ∀ k, flow ≤ f (x k))
    (ε : ℝ) (hε : 0 < ε) (α p : ℝ) (hα : 0 < α) (hp : 0 < p) (j : ℕ)
    (h26 : ∀ k ≤ j, model f (B k) (σ k) (x k) (s k) < f (x k))
    (So : Finset ℕ)
    (hSo : So ⊆ (Finset.range (j + 1)).filter (fun k => η₁ ≤ rho f (B k) (σ k) (x k) (s k)))
    (h218 : ∀ k ∈ So, α * ε ^ p ≤ f (x k) - model f (B k) (σ k) (x k) (s k)) :
    (So.card : ℤ) ≤ ⌈(f (x 0) - flow) / (η₁ * α) * ε ^ (-p)⌉ := by sorry

end AdaptiveCubic.Cauchy
