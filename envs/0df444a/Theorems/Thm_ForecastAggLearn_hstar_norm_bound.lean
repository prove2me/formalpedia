-- Prove2me | Theorems.Thm_ForecastAggLearn_hstar_norm_bound
-- name    : ForecastAggLearn.hstar_norm_bound
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:26:33.284998+00:00
-- url     : https://prove2.me/theorems/fbd480e5-cb45-4e54-b84e-f88a207e8558
-- title:
--   §4.2.1 — $\|h^*\|^2\le m/\sigma_{\min}(A)^2\le n/\sigma^2=W^2$
-- statement:
--   Let $A$ be a real $n\times m$ matrix and $\sigma>0$ with $\sigma_{\min}(A)\ge\sigma$, i.e. $\sigma\|y\|\le\|Ay\|$ for every $y\in\mathbb R^m$. Then $A$ is injective, $m\le n$, and $h^*=A(A^\top A)^{-1}\mathbf 1_m$ satisfies
--
--   $$
--   \|h^*\|^2\le\frac{m}{\sigma^2}\le\frac{n}{\sigma^2},\qquad\text{so}\qquad \|h^*\|\le\frac{\sqrt n}{\sigma}=W .
--   $$
--
--   This is the verification that the ball of radius $W=\sigma^{-1}\sqrt n$ used by online gradient descent contains the optimal aggregation vector $h^*$.
--
--   **Formalization Note** Norms are Euclidean. $\sigma_{\min}(A)\ge\sigma$, where $\sigma_{\min}(A)^2$ is the least eigenvalue of $A^\top A$ (p.12), is encoded as $\sigma\|y\|\le\|Ay\|$ for all $y$; for $m\ge1$ the two are the same.
--
--   Differences from the source:
--   - generalization: A the 0/1 evidence matrix → any real n × m matrix; reason: the evidence matrix is the 0/1 case
--   - encoding: σ_min(A) ≥ σ with σ_min(A)² = λ_min(AᵀA); ‖h*‖² ≤ m/σ_min(A)² ≤ n/σ² → σ‖y‖ ≤ ‖Ay‖ for all y; ‖h*‖² ≤ m/σ², m ≤ n, ‖h*‖ ≤ √n/σ; reason: the norm inequality is λ_min(AᵀA) ≥ σ² for m ≥ 1; taking σ = σ_min(A) gives the middle bound
-- source:
--   Babichenko, Garber, Learning of Optimal Forecast Aggregation in Partial Evidence Environments, arXiv:1802.07107v1, §4.2.1, display, p.19

import Mathlib
import Definitions.Def_ForecastAggLearn_hstar

namespace ForecastAggLearn

/-- **Norm bound on `h*`.**
Babichenko, Garber, arXiv:1802.07107v1, §4.2.1, display, p.19:
`‖A_l^{−1⊤} 1_m‖²₂ = ‖A(A^⊤A)^{−1} 1_m‖²₂ ≤ ‖A(A^⊤A)^{−1}‖²₂ · ‖1_m‖²₂ = m · ‖Σ^{−1}‖²₂
= m / σ_min(A)² ≤ n/σ² = W²`, "where the last inequality holds using the fact that A is
injective, which implies that m ≤ n, and our assumption that σ_min(A) ≥ σ."

For `σ > 0` with `σ_min(A) ≥ σ`: `‖h*‖² ≤ m/σ²`, `m ≤ n`, and `‖h*‖ ≤ √n/σ = W`.

**Formalization Note.** `σ_min(A) ≥ σ` (with `σ_min(A)²` the least eigenvalue of `A^⊤A`, p.12)
is encoded as `σ‖y‖ ≤ ‖Ay‖` for all `y ∈ ℝ^m`, Euclidean norms; it implies that `A` is
injective. Stated for every real `n × m` matrix (the evidence matrix is the 0/1 case). -/
theorem hstar_norm_bound {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (σ : ℝ) (hσ : 0 < σ)
    (hA : ∀ y : EuclideanSpace ℝ (Fin m),
      σ * ‖y‖ ≤ ‖(WithLp.toLp 2 (A.mulVec y.ofLp) : EuclideanSpace ℝ (Fin n))‖) :
    ‖(WithLp.toLp 2 (hstar A) : EuclideanSpace ℝ (Fin n))‖ ^ 2 ≤ m / σ ^ 2 ∧ m ≤ n ∧
      ‖(WithLp.toLp 2 (hstar A) : EuclideanSpace ℝ (Fin n))‖ ≤ Real.sqrt n / σ := by sorry

end ForecastAggLearn
