-- Prove2me | Theorems.Thm_FixedRankGeom_PSD_theorem_3
-- name    : FixedRankGeom.PSD.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:37:42.10426+00:00
-- url     : https://prove2.me/theorems/391d87d3-0c95-49ae-9f69-a6b56cc52166
-- title:
--   Theorem 3, p. 21 — embedded vs YYᵀ-quotient geometry on rank-r PSD matrices: gradient identities, Hessian identity at FOSPs, eigenvalue sandwich
-- statement:
--   Let $0<r\le p$ and let $f:\mathbb R^{p\times p}\to\mathbb R$ be twice continuously differentiable with $f(X^\top)=f(X)$. Let $Y\mapsto W_Y$ be smooth and symmetric positive definite on $\mathbb R_*^{p\times r}$, and assume $W_Y=OW_{YO}O^\top$ for every $Y\in\mathbb R_*^{p\times r}$ and $O\in\mathbb O_r$. Fix $Y\in\mathbb R_*^{p\times r}$, let $X=YY^\top$, let $U\in\mathrm{St}(r,p)$ span the top $r$ eigenspace of $X$, $P=U^\top Y$ and $Y^\dagger=(Y^\top Y)^{-1}Y^\top$. Write $\operatorname{grad} f(X)$, $\operatorname{Hess} f(X)$ for the Riemannian gradient and Hessian on the embedded manifold $\mathcal M^e_{r+}$ (Frobenius metric), and $\overline{\operatorname{grad} h_{r+}([Y])}$, $\overline{\operatorname{Hess} h_{r+}([Y])}$ for the horizontal lifts of those of $h_{r+}([Y])$, induced by $\bar h_{r+}(Y)=f(YY^\top)$ on the quotient $\mathcal M^{q_1}_{r+}=\mathbb R_*^{p\times r}/\mathbb O_r$ with metric $\bar g_Y(\eta,\theta)=\operatorname{tr}(W_Y\eta^\top\theta)$. Then
--
--   1. the gradients are related by
--   $$\operatorname{grad} f(X)=\Big(\overline{\operatorname{grad} h_{r+}([Y])}W_YY^\dagger+\big(\overline{\operatorname{grad} h_{r+}([Y])}W_YY^\dagger\big)^\top(I_p-YY^\dagger)\Big)/2,\qquad \overline{\operatorname{grad} h_{r+}([Y])}=2\operatorname{grad} f(X)\,YW_Y^{-1};\qquad(34)$$
--   2. if $[Y]$ is a Riemannian first-order stationary point of (18a), i.e. $\overline{\operatorname{grad} h_{r+}([Y])}=0$, then
--   $$\overline{\operatorname{Hess} h_{r+}([Y])}[\theta_Y,\theta_Y]=\operatorname{Hess} f(X)[\mathcal L^{r+}_Y(\theta_Y),\mathcal L^{r+}_Y(\theta_Y)]\quad\forall\theta_Y\in\mathcal H_Y\bar{\mathcal M}^{q_1}_{r+},\qquad(35)$$
--   with $\mathcal L^{r+}_Y(\theta)=Y\theta^\top+\theta Y^\top$; both Hessians have $d=pr-(r^2-r)/2$ eigenvalues (the dimensions of $\mathcal H_Y\bar{\mathcal M}^{q_1}_{r+}$ and $T_X\mathcal M^e_{r+}$); and for $i=1,\dots,d$, $\lambda_i\big(\overline{\operatorname{Hess} h_{r+}([Y])}\big)$ is sandwiched between
--   $$2\sigma_r(PW_Y^{-1}P^\top)\,\lambda_i(\operatorname{Hess} f(X))\quad\text{and}\quad4\sigma_1(PW_Y^{-1}P^\top)\,\lambda_i(\operatorname{Hess} f(X)).$$
--
--   This is the paper's first main result: at stationary points, the embedded and the full-rank-factorization quotient geometries see the same second-order landscape, with eigenvalues of the same sign and comparable size, so first- and second-order stationarity and strict saddles correspond.
--
--   **Formalization Note** $\lambda_i$ is the $i$-th largest eigenvalue as the max–min value of the quadratic form with respect to the metric of each space ($\bar g_Y$ on $\mathcal H_Y$, Frobenius on $T_X$). $\operatorname{Hess} f(X)$ enters as any function satisfying the curve characterisation of the embedded Hessian (which determines it on $T_X\mathcal M^e_{r+}$; existence is Proposition 1). "Sandwiched" means $\min(a,b)\le\mu\le\max(a,b)$. "$U$ spans the top $r$ eigenspace of $X$" is encoded as $U^\top U=I_r$ and $UU^\top Y=Y$. The metric hypotheses (positive definite, smooth) encode "$\bar g$ is a Riemannian metric" (Remark 1); $f$ symmetric and $C^2$ are the standing assumptions of p. 2.
-- source:
--   Luo, Li & Zhang, On Geometric Connections of Embedded and Quotient Geometries in Riemannian Fixed-rank Matrix Optimization, arXiv:2110.12121v2, p. 21, Theorem 3, (34)–(35); conditions of Proposition 2 p. 18; standing assumptions p. 2

import Mathlib
import Definitions.Def_FixedRankGeom_PSD_Model

open scoped RealInnerProductSpace Matrix ContDiff
open ProjLikeRetr.Retractor

namespace FixedRankGeom.PSD

/-- Theorem 3, p. 21: geometric landscape connections of (1) on `M^e_{r+}` and `M^{q1}_{r+}`. -/
theorem theorem_3 {p r : ℕ} (hr : 0 < r) (hrp : r ≤ p)
    (f : Mat p p → ℝ) (hf : ContDiff ℝ 2 f) (hfs : ∀ X, f (ofMat (toMat X)ᵀ) = f X)
    (W : Mat p r → Mat r r)
    (hWpd : ∀ Y ∈ fullRankSet p r, (toMat (W Y)).PosDef) (hWs : ContDiffOn ℝ ∞ W (fullRankSet p r))
    (hWinv : ∀ Y ∈ fullRankSet p r, ∀ O ∈ Matrix.orthogonalGroup (Fin r) ℝ,
      toMat (W Y) = O * toMat (W (ofMat (toMat Y * O))) * Oᵀ)
    (Y : Mat p r) (hY : Y ∈ fullRankSet p r)
    (U : Matrix (Fin p) (Fin r) ℝ) (hU : Uᵀ * U = 1) (hUY : U * Uᵀ * toMat Y = toMat Y) :
    let X := gram Y
    let P := Uᵀ * toMat Y
    let Wm := toMat (W Y)
    let Ydag := ((toMat Y)ᵀ * toMat Y)⁻¹ * (toMat Y)ᵀ
    let gradf := toMat (ZORiem.RGD.rgrad (psdRankSet p r) f X)
    let gradh := toMat (quotGrad W (hbarOf f) Y)
    let d := p * r - (r ^ 2 - r) / 2
    -- (34)
    gradf = (1 / 2 : ℝ) • (gradh * Wm * Ydag + (gradh * Wm * Ydag)ᵀ * (1 - toMat Y * Ydag)) ∧
    gradh = (2 : ℝ) • (gradf * toMat Y * Wm⁻¹) ∧
    -- at a Riemannian FOSP [Y] of (18a): (35), the eigenvalue count, and the sandwich
    (quotGrad W (hbarOf f) Y = 0 → ∀ q, IsEmbHessQuad (psdRankSet p r) f X q →
      (∀ θ ∈ horizontalSpace W Y, totalHessQuad W (hbarOf f) Y θ = q (Lmap Y θ)) ∧
      Module.finrank ℝ (horizontalSpace W Y) = d ∧
      Module.finrank ℝ (tangentSpace (psdRankSet p r) X) = d ∧
      ∀ i, 1 ≤ i → i ≤ d →
        IsSandwiched (kthEig (qmetric W Y) (totalHessQuad W (hbarOf f) Y) (horizontalSpace W Y) i)
          (2 * sigmaMin (P * Wm⁻¹ * Pᵀ) *
            kthEig (fun a b => ⟪a, b⟫) q (tangentSpace (psdRankSet p r) X) i)
          (4 * sigmaMax (P * Wm⁻¹ * Pᵀ) *
            kthEig (fun a b => ⟪a, b⟫) q (tangentSpace (psdRankSet p r) X) i)) := by sorry

end FixedRankGeom.PSD
