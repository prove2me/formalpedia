-- Prove2me | Theorems.Thm_BarrierTR_Global_lemma_2_2
-- name    : BarrierTR.Global.lemma_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T16:56:41.043656+00:00
-- url     : https://prove2.me/theorems/89e95a6a-9ee1-4aa9-a6ad-d10fb80d5b34
-- title:
--   Lemma 2.2, p. 13 — vertical Cauchy decrease: ‖g+s‖ vpred(v) ≥ (γ₁/2)‖(A;S)(g+s)‖ min(γ_T, γ_TΔ̃/β̂, ‖(A;S)(g+s)‖/‖(Aᵀ S)‖²)
-- statement:
--   Let $(x_k,s_k)$ be an iterate with $s_k>0$, and write $g_k=g(x_k)$, $A_k=A(x_k)$, $S_k=\operatorname{diag}(s_k)$. Let $\|\cdot\|_T$ be a norm on $\mathbb R^{n+m}$ and $\gamma_T\in(0,1)$ a constant with $\gamma_T\|u\|\le\|u\|_T\le\gamma_T^{-1}\|u\|$ for all $u$ (2.22); let $\beta>0$, $\hat\beta=\max(1,\beta)$ (2.23), $\tilde\Delta_k>0$ and $\gamma_1>0$. Suppose that $v_k=(v_x,v_s)$ is an approximate solution of the vertical problem (2.9) satisfying the vertical Cauchy decrease condition (2.18). Then
--   $$\|g_k+s_k\|\,\mathrm{vpred}_k(v_k)\ \ge\ \frac{\gamma_1}{2}\Big\|\binom{A_k}{S_k}(g_k+s_k)\Big\|\min\Big(\gamma_T,\ \frac{\gamma_T\tilde\Delta_k}{\hat\beta},\ \frac{\|(A_k;S_k)(g_k+s_k)\|}{\|(A_k^\top\ S_k)\|^2}\Big).\qquad(2.24)$$
--
--   This lower bound on the vertical predicted reduction drives the feasibility analysis (Lemmas 4.5 and 4.8).
--
--   **Formalization Note** "Smooth" (p. 1) is read as $C^1$: $f$ and $g$ are continuously differentiable on all of $\mathbb R^n$. Vectors live in `EuclideanSpace`, stacked vectors $(a,b)$ in `WithLp 2` products, so every $\|\cdot\|$ is the Euclidean norm (spectral norm for matrices). $A(x)$ is the adjoint of the derivative of $g$, so $A(x)^\top d_x$ is `fderiv ℝ g x d_x`. An approximate solution of (2.9) is read as a feasible point of (2.9); $\|(A_k^\top\ S_k)\|$ is the spectral norm of the $m\times(n+m)$ matrix.
-- source:
--   Byrd, Gilbert, Nocedal, A trust region method based on interior point techniques for nonlinear programming, INRIA RR-2896 (1996), HAL inria-00073794v1, p. 13, Lemma 2.2, (2.22)–(2.24)

import Mathlib
import Definitions.Def_BarrierTR_Global_Setting
open scoped RealInnerProductSpace
open Filter Topology

namespace BarrierTR.Global

/-- Lemma 2.2 (p. 13). If `s > 0` and `v` is a feasible approximate solution of the vertical
problem (2.9) (radius `Δ̃`) satisfying the vertical Cauchy decrease condition (2.18), then (2.24):
`‖g + s‖ vpred(v) ≥ (γ₁/2) ‖(A; S)(g + s)‖ min(γ_T, γ_T Δ̃/β̂, ‖(A; S)(g + s)‖/‖(Aᵀ S)‖²)`,
where `γ_T ∈ (0, 1)` is a norm-equivalence constant (2.22) and `β̂ = max(1, β)` (2.23). -/
theorem lemma_2_2 {n m : ℕ} (g : E n → F m) (hg : ContDiff ℝ 1 g)
    (x : E n) (s : F m) (hs : ∀ i, 0 < s i)
    (T : Seminorm ℝ (Z n m)) (hT : ∀ z, T z = 0 → z = 0)
    (γT : ℝ) (hγT : 0 < γT ∧ γT < 1) (hTeq : ∀ u : Z n m, γT * ‖u‖ ≤ T u ∧ T u ≤ γT⁻¹ * ‖u‖)
    (β Δt γ₁ : ℝ) (hβ : 0 < β) (hΔt : 0 < Δt) (hγ₁ : 0 < γ₁)
    (v : Z n m) (hfeas : VertFeasible T β Δt s v) (hcauchy : VertCauchy T β Δt γ₁ g x s v) :
    γ₁ / 2 * ‖stackAS g x s (g x + s)‖ *
        min (min γT (γT * Δt / max 1 β)) (‖stackAS g x s (g x + s)‖ / ‖rowATS g x s‖ ^ 2)
      ≤ ‖g x + s‖ * vpred g x s v := by sorry

end BarrierTR.Global
