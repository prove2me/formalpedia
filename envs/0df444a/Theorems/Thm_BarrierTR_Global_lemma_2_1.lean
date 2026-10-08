-- Prove2me | Theorems.Thm_BarrierTR_Global_lemma_2_1
-- name    : BarrierTR.Global.lemma_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T16:55:30.609586+00:00
-- url     : https://prove2.me/theorems/2c49feae-171a-41cd-8bdf-d9748b1a370d
-- title:
--   Lemma 2.1, p. 12 — −ψ_min ≥ (|qᵀd|/2) min(Δ/‖Ld‖_T, |qᵀd|/(dᵀQd)⁺) along a descent direction
-- statement:
--   Let $V$ be a real inner product space, $q\in V$, $Q$ a symmetric linear map on $V$, $L$ a nonzero linear map from $V$ into a real vector space carrying a norm $\|\cdot\|_T$, and $\Delta>0$. Consider the quadratic program
--   $$\min\ \psi(z)=q^\top z+\tfrac12 z^\top Qz\quad\text{s.t.}\quad\|Lz\|_T\le\Delta.$$
--   For any direction $d$ with $q^\top d\le0$ and $Ld\ne0$, the minimum value of $\psi$ along $d$ within the trust region, $\psi_{\min}=\min\{\psi(\alpha d):\|\alpha Ld\|_T\le\Delta\}$, satisfies
--   $$-\psi_{\min}\ \ge\ \frac{|q^\top d|}{2}\,\min\Big(\frac{\Delta}{\|Ld\|_T},\ \frac{|q^\top d|}{(d^\top Qd)^+}\Big),\qquad(\cdot)^+=\max(0,\cdot),$$
--   where the second entry is $+\infty$ when $d^\top Qd\le0$.
--
--   This generalizes Powell's Cauchy-point bound ($L=I$, $d=-q$) and is applied to the vertical and horizontal subproblems in Lemmas 2.2 and 2.3.
--
--   **Formalization Note** The case $d^\top Qd\le0$, where the paper divides by $(d^\top Qd)^+=0$ and means $+\infty$, is split off explicitly; the bound is then $\frac{|q^\top d|}{2}\frac{\Delta}{\|Ld\|_T}$. $\psi_{\min}$ is the infimum of $\psi(\alpha d)$ over the feasible $\alpha$; the feasible set is the compact interval $|\alpha|\le\Delta/\|Ld\|_T$, so the infimum is attained.
-- source:
--   Byrd, Gilbert, Nocedal, A trust region method based on interior point techniques for nonlinear programming, INRIA RR-2896 (1996), HAL inria-00073794v1, p. 12, Lemma 2.1, (2.21)

import Mathlib
open scoped RealInnerProductSpace
open Filter Topology

namespace BarrierTR.Global

/-- Lemma 2.1 (p. 12). For `ψ(z) = qᵀz + ½ zᵀQz`, `Q` symmetric, `L ≠ 0`, `Δ > 0` and a norm
`‖·‖_T`: for any `d` with `qᵀd ≤ 0` and `Ld ≠ 0`, `ψ_min = min{ψ(αd) : ‖αLd‖_T ≤ Δ}` satisfies
`−ψ_min ≥ (|qᵀd|/2) min(Δ/‖Ld‖_T, |qᵀd|/(dᵀQd)⁺)`, the second entry being `+∞` when `dᵀQd ≤ 0`. -/
theorem lemma_2_1 {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [AddCommGroup W] [Module ℝ W]
    (q : V) (Q : V →ₗ[ℝ] V) (hQ : Q.IsSymmetric) (L : V →ₗ[ℝ] W) (hL : L ≠ 0)
    (T : Seminorm ℝ W) (hT : ∀ w, T w = 0 → w = 0) (Δ : ℝ) (hΔ : 0 < Δ)
    (d : V) (hqd : ⟪q, d⟫ ≤ 0) (hLd : L d ≠ 0) :
    (if ⟪d, Q d⟫ ≤ 0 then |⟪q, d⟫| / 2 * (Δ / T (L d))
      else |⟪q, d⟫| / 2 * min (Δ / T (L d)) (|⟪q, d⟫| / ⟪d, Q d⟫))
      ≤ -sInf {y : ℝ | ∃ α : ℝ, T (α • L d) ≤ Δ ∧
          y = ⟪q, α • d⟫ + (1 / 2) * ⟪α • d, Q (α • d)⟫} := by sorry

end BarrierTR.Global
