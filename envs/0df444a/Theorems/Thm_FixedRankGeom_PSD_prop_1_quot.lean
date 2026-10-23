-- Prove2me | Theorems.Thm_FixedRankGeom_PSD_prop_1_quot
-- name    : FixedRankGeom.PSD.prop_1_quot
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:37:34.258122+00:00
-- url     : https://prove2.me/theorems/a9ecf50f-d174-46c5-b2d5-c20c2f4b8d7b
-- title:
--   Proposition 1, second bullet (on M^{q1}_{r+}), (20), p. 17 — quotient Riemannian gradient and Hessian
-- statement:
--   Let $0<r\le p$ and let $f:\mathbb R^{p\times p}\to\mathbb R$ be twice continuously differentiable with $f(X^\top)=f(X)$. Let the weight $Y\mapsto W_Y$ be smooth and symmetric positive definite on $\mathbb R_*^{p\times r}$, giving the metric $\bar g_Y(\eta,\theta)=\operatorname{tr}(W_Y\eta^\top\theta)$, and let $\bar h_{r+}(Y)=f(YY^\top)$. For $Y\in\mathbb R_*^{p\times r}$:
--
--   1. the horizontal lift of the quotient gradient is
--   $$\overline{\operatorname{grad} h_{r+}([Y])}=2\nabla f(YY^\top)YW_Y^{-1};$$
--   2. for every horizontal $\theta_Y\in\mathcal H_Y\bar{\mathcal M}^{q_1}_{r+}$,
--   $$\begin{aligned}\overline{\operatorname{Hess} h_{r+}([Y])}[\theta_Y,\theta_Y]={}&\nabla^2 f(YY^\top)[Y\theta_Y^\top+\theta_YY^\top,\,Y\theta_Y^\top+\theta_YY^\top]+2\langle\nabla f(YY^\top),\theta_Y\theta_Y^\top\rangle\\&+2\langle\nabla f(YY^\top)Y\,\mathrm DW_Y^{-1}[\theta_Y],\,\theta_YW_Y\rangle+\big\langle\mathrm DW_Y\big[\overline{\operatorname{grad} h_{r+}([Y])}\big],\,\theta_Y^\top\theta_Y\big\rangle/2.\end{aligned}\qquad(20)$$
--
--   Here $\mathrm DW_Y^{-1}[\theta]$ and $\mathrm DW_Y[\eta]$ are the directional derivatives of $Z\mapsto W_Z^{-1}$ and $Z\mapsto W_Z$ at $Y$. The left side of (20) is the Hessian quadratic form of $\bar h_{r+}$ for $\bar g$, given by the Koszul formula. Formula (20) is the quotient side of the Hessian identity (35) of Theorem 3.
--
--   **Formalization Note** "$W_Y\in\mathbb S_+(r)$ defines a Riemannian metric" (Remark 1) is encoded as: $W_Y$ positive definite for every full-rank $Y$ and $W$ smooth on $\mathbb R_*^{p\times r}$. The invariance $W_Y=OW_{YO}O^\top$ is not assumed here, as in the paper's bullet.
-- source:
--   Luo, Li & Zhang, On Geometric Connections of Embedded and Quotient Geometries in Riemannian Fixed-rank Matrix Optimization, arXiv:2110.12121v2, p. 17, Proposition 1, second bullet (on M^{q1}_{r+}), (20); (18a) p. 17; Remark 1 p. 11; standing assumptions p. 2

import Mathlib
import Definitions.Def_FixedRankGeom_PSD_Model

open scoped RealInnerProductSpace Matrix ContDiff
open ProjLikeRetr.Retractor

namespace FixedRankGeom.PSD

/-- Proposition 1, second bullet (on `M^{q1}_{r+}`), (20), p. 17. -/
theorem prop_1_quot {p r : ℕ} (hr : 0 < r) (hrp : r ≤ p)
    (f : Mat p p → ℝ) (hf : ContDiff ℝ 2 f) (hfs : ∀ X, f (ofMat (toMat X)ᵀ) = f X)
    (W : Mat p r → Mat r r)
    (hWpd : ∀ Y ∈ fullRankSet p r, (toMat (W Y)).PosDef) (hWs : ContDiffOn ℝ ∞ W (fullRankSet p r))
    (Y : Mat p r) (hY : Y ∈ fullRankSet p r) :
    let X := gram Y
    let G := toMat (gradient f X)
    let gradh := quotGrad W (hbarOf f) Y
    toMat gradh = (2 : ℝ) • (G * toMat Y * (toMat (W Y))⁻¹) ∧
    ∀ θ ∈ horizontalSpace W Y,
      let Lθ := ofMat (toMat Y * (toMat θ)ᵀ + toMat θ * (toMat Y)ᵀ)
      let DWinv := toMat (fderiv ℝ (fun Z => ofMat (toMat (W Z))⁻¹) Y θ)
      totalHessQuad W (hbarOf f) Y θ =
        iteratedFDeriv ℝ 2 f X ![Lθ, Lθ] + 2 * ⟪gradient f X, ofMat (toMat θ * (toMat θ)ᵀ)⟫
          + 2 * ⟪ofMat (G * toMat Y * DWinv), ofMat (toMat θ * toMat (W Y))⟫
          + ⟪fderiv ℝ W Y gradh, ofMat ((toMat θ)ᵀ * toMat θ)⟫ / 2 := by sorry

end FixedRankGeom.PSD
