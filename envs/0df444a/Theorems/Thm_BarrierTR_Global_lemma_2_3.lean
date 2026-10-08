-- Prove2me | Theorems.Thm_BarrierTR_Global_lemma_2_3
-- name    : BarrierTR.Global.lemma_2_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T16:57:10.954155+00:00
-- url     : https://prove2.me/theorems/75bf3fe3-112d-41ae-9904-5362476ab78a
-- title:
--   Lemma 2.3, p. 16 — horizontal Cauchy decrease: hpred(h) ≥ (γ₂/2)‖p^c‖ min(γ_TΔ̂/‖Z_xᵀZ_x+Z_sᵀD²Z_s‖^{1/2}, ‖p^c‖/‖Z_xᵀBZ_x+μZ_sᵀS⁻²Z_s‖)
-- statement:
--   Let $(x_k,s_k)$ be an iterate with $s_k>0$, $B_k$ symmetric, $\mu>0$, and $Z_k=(Z_x^\top\ Z_s^\top)^\top$ a null-space basis satisfying (2.29)–(2.30) with $\gamma_Z>0$. Let $\|\cdot\|_T$ and $\gamma_T\in(0,1)$ satisfy (2.22), $\beta,\Delta_k,\hat\Delta_k,\gamma_2>0$, and $D_k=\max(\beta,\Delta_k)S_k^{-1}$. If the horizontal step $h_k=(h_x,h_s)$ (for a vertical step $v_k$) satisfies the horizontal Cauchy decrease condition (2.33), then
--   $$\mathrm{hpred}_k(h_k)\ \ge\ \frac{\gamma_2}{2}\|p_k^c\|\min\Big(\frac{\gamma_T\hat\Delta_k}{\|Z_x^\top Z_x+Z_s^\top D_k^2Z_s\|^{1/2}},\ \frac{\|p_k^c\|}{\|Z_x^\top B_kZ_x+\mu Z_s^\top S_k^{-2}Z_s\|}\Big),\qquad(2.36)$$
--   with $p_k^c$ from (2.32).
--
--   This bound is what makes the horizontal step reduce the barrier objective in Theorem 4.10.
--
--   **Formalization Note** "Smooth" (p. 1) is read as $C^1$: $f$ and $g$ are continuously differentiable on all of $\mathbb R^n$. Vectors live in `EuclideanSpace`, stacked vectors $(a,b)$ in `WithLp 2` products, so every $\|\cdot\|$ is the Euclidean norm (spectral norm for matrices). $A(x)$ is the adjoint of the derivative of $g$, so $A(x)^\top d_x$ is `fderiv ℝ g x d_x`. When $Z_x^\top B_kZ_x+\mu Z_s^\top S_k^{-2}Z_s=0$ the second entry of the minimum is $+\infty$ and the bound is the first entry alone; this case is split off explicitly. $\hat\Delta_k>0$ is assumed, as Algorithm I guarantees through (2.27). As on the page, feasibility of $h_k$ for (2.26) is not assumed: only (2.33) is.
-- source:
--   Byrd, Gilbert, Nocedal, A trust region method based on interior point techniques for nonlinear programming, INRIA RR-2896 (1996), HAL inria-00073794v1, p. 16, Lemma 2.3, (2.36)

import Mathlib
import Definitions.Def_BarrierTR_Global_Setting
open scoped RealInnerProductSpace
open Filter Topology

namespace BarrierTR.Global

/-- Lemma 2.3 (p. 16). If `s > 0`, `Z = (Z_xᵀ Z_sᵀ)ᵀ` satisfies (2.29)–(2.30), and `h` satisfies the
horizontal Cauchy decrease condition (2.33) (radii `Δ`, `Δ̂ > 0`), then (2.36):
`hpred(h) ≥ (γ₂/2)‖p^c‖ min(γ_T Δ̂/‖Z_xᵀZ_x + Z_sᵀD²Z_s‖^{1/2}, ‖p^c‖/‖Z_xᵀBZ_x + μZ_sᵀS⁻²Z_s‖)`,
with `D = max(β, Δ) S⁻¹`; the second entry is `+∞` when its denominator vanishes. -/
theorem lemma_2_3 {n m : ℕ} (f : E n → ℝ) (g : E n → F m) (hf : ContDiff ℝ 1 f)
    (hg : ContDiff ℝ 1 g) (μ : ℝ) (hμ : 0 < μ)
    (x : E n) (s : F m) (hs : ∀ i, 0 < s i) (B : E n →L[ℝ] E n) (hB : IsSelfAdjoint B)
    (Zx : E n →L[ℝ] E n) (Zs : E n →L[ℝ] F m) (γZ : ℝ) (hγZ : 0 < γZ)
    (hZ : IsNullBasis g x γZ Zx Zs)
    (T : Seminorm ℝ (Z n m)) (hT : ∀ z, T z = 0 → z = 0)
    (γT : ℝ) (hγT : 0 < γT ∧ γT < 1) (hTeq : ∀ u : Z n m, γT * ‖u‖ ≤ T u ∧ T u ≤ γT⁻¹ * ‖u‖)
    (β Δ Δhat γ₂ : ℝ) (hβ : 0 < β) (hΔ : 0 < Δ) (hΔhat : 0 < Δhat) (hγ₂ : 0 < γ₂)
    (v h : Z n m)
    (hcauchy : HorizCauchy T β Δ Δhat γ₂ f μ x s B Zx Zs v h) :
    let p := pc f μ x s B Zx Zs v
    let M₁ : E n →L[ℝ] E n := ContinuousLinearMap.adjoint Zx ∘L Zx +
      ContinuousLinearMap.adjoint Zs ∘L diagL (fun i => (max β Δ / s i) ^ 2) ∘L Zs
    let M₂ : E n →L[ℝ] E n := ContinuousLinearMap.adjoint Zx ∘L B ∘L Zx +
      μ • (ContinuousLinearMap.adjoint Zs ∘L diagL (fun i => 1 / s i ^ 2) ∘L Zs)
    (if ‖M₂‖ = 0 then γ₂ / 2 * ‖p‖ * (γT * Δhat / ‖M₁‖ ^ ((1 : ℝ) / 2))
      else γ₂ / 2 * ‖p‖ * min (γT * Δhat / ‖M₁‖ ^ ((1 : ℝ) / 2)) (‖p‖ / ‖M₂‖))
      ≤ hpred f μ x s B v h := by sorry

end BarrierTR.Global
