-- Prove2me | Theorems.Thm_FixedRankGeom_PSD_prop_2_spectrum
-- name    : FixedRankGeom.PSD.prop_2_spectrum
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:37:38.572174+00:00
-- url     : https://prove2.me/theorems/33a0f565-50ef-488d-8569-92d70774ad88
-- title:
--   Proposition 2, spectrum bound (23), p. 18 — 2σ_r(PW⁻¹Pᵀ) ḡ(θ,θ) ≤ ‖L(θ)‖²_F ≤ 4σ_1(PW⁻¹Pᵀ) ḡ(θ,θ)
-- statement:
--   Let $0<r\le p$, $Y\in\mathbb R_*^{p\times r}$, $X=YY^\top$, and let $W_Y$ be symmetric positive definite. Let $U\in\mathrm{St}(r,p)$ span the top $r$ eigenspace of $X$ (encoded as $UU^\top Y=Y$) and $P=U^\top Y$. Then for every horizontal $\theta_Y\in\mathcal H_Y\bar{\mathcal M}^{q_1}_{r+}$,
--   $$2\sigma_r(PW_Y^{-1}P^\top)\,\bar g_Y(\theta_Y,\theta_Y)\le\big\|\mathcal L^{r+}_Y(\theta_Y)\big\|_F^2\le4\sigma_1(PW_Y^{-1}P^\top)\,\bar g_Y(\theta_Y,\theta_Y),\qquad(23)$$
--   where $\mathcal L^{r+}_Y(\theta)=Y\theta^\top+\theta Y^\top$, $\bar g_Y(\theta,\theta)=\operatorname{tr}(W_Y\theta^\top\theta)$, and $\sigma_1,\sigma_r$ are the largest and smallest singular values of the symmetric positive definite matrix $PW_Y^{-1}P^\top$.
--
--   These are the constants $\alpha,\beta$ fed into the sandwich Theorem 2 to obtain the eigenvalue comparison of Theorem 3.
--
--   **Formalization Note** $\|\cdot\|_F$ is the Euclidean norm of $\mathbb R^{p\times p}$ viewed as `EuclideanSpace`. $\sigma_1$ and $\sigma_r$ are computed as the largest and smallest Rayleigh quotients, which coincide with the extreme singular values for a symmetric positive definite matrix.
-- source:
--   Luo, Li & Zhang, On Geometric Connections of Embedded and Quotient Geometries in Riemannian Fixed-rank Matrix Optimization, arXiv:2110.12121v2, p. 18, Proposition 2, spectrum bound (23)

import Mathlib
import Definitions.Def_FixedRankGeom_PSD_Model

open scoped RealInnerProductSpace Matrix ContDiff
open ProjLikeRetr.Retractor

namespace FixedRankGeom.PSD

/-- Proposition 2, spectrum bound (23), p. 18. -/
theorem prop_2_spectrum {p r : ℕ} (hr : 0 < r) (hrp : r ≤ p)
    (W : Mat p r → Mat r r) (Y : Mat p r) (hY : Y ∈ fullRankSet p r)
    (hW : (toMat (W Y)).PosDef)
    (U : Matrix (Fin p) (Fin r) ℝ) (hU : Uᵀ * U = 1) (hUY : U * Uᵀ * toMat Y = toMat Y) :
    let P := Uᵀ * toMat Y
    ∀ θ ∈ horizontalSpace W Y,
      2 * sigmaMin (P * (toMat (W Y))⁻¹ * Pᵀ) * qmetric W Y θ θ ≤ ‖Lmap Y θ‖ ^ 2 ∧
      ‖Lmap Y θ‖ ^ 2 ≤ 4 * sigmaMax (P * (toMat (W Y))⁻¹ * Pᵀ) * qmetric W Y θ θ := by sorry

end FixedRankGeom.PSD
