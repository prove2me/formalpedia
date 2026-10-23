-- Prove2me | Theorems.Thm_FixedRankGeom_PSD_prop_1_emb
-- name    : FixedRankGeom.PSD.prop_1_emb
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:37:38.987965+00:00
-- url     : https://prove2.me/theorems/73eb254c-c276-46ca-bd92-cc41cd4add7f
-- title:
--   Proposition 1, first bullet (on M^e_{r+}), (19), p. 17 — embedded Riemannian gradient and Hessian
-- statement:
--   Let $0<r\le p$ and let $f:\mathbb R^{p\times p}\to\mathbb R$ be twice continuously differentiable with $f(X^\top)=f(X)$. Let $X\in\mathcal M_{r+}$, let $[U\ U_\perp]$ be a $p\times p$ orthogonal matrix whose block $U\in\mathrm{St}(r,p)$ spans the top $r$ eigenspace of $X$, write $P_U=UU^\top$, $P_{U_\perp}=U_\perp U_\perp^\top$ and $\Sigma=U^\top XU$. Then
--
--   1. the Riemannian gradient of $f$ on $\mathcal M^e_{r+}$ (induced Frobenius metric) is
--   $$\operatorname{grad} f(X)=P_U\nabla f(X)P_U+P_{U_\perp}\nabla f(X)P_U+P_U\nabla f(X)P_{U_\perp};$$
--   2. the Riemannian Hessian quadratic form of $f$ at $X$ exists, and for every tangent vector $\xi_X=[U\ U_\perp]\begin{bmatrix}S&D^\top\\D&0\end{bmatrix}[U\ U_\perp]^\top$ with $S\in\mathbb S^{r\times r}$, $D\in\mathbb R^{(p-r)\times r}$,
--   $$\operatorname{Hess} f(X)[\xi_X,\xi_X]=\nabla^2 f(X)[\xi_X,\xi_X]+2\big\langle\nabla f(X),\,U_\perp D\Sigma^{-1}D^\top U_\perp^\top\big\rangle.\qquad(19)$$
--
--   Here $\nabla f$ and $\nabla^2 f$ are the Euclidean gradient and Hessian, and $\langle\cdot,\cdot\rangle$ is the Frobenius inner product. The formula (19) is the embedded side of the Hessian identity (35) of Theorem 3.
--
--   **Formalization Note** The Hessian is the curve-defined quadratic form of the mission's definitions; item 2 states both that such a form exists (so statements quantifying over it are not vacuous) and that every such form is given by (19) on the tangent space. $\nabla^2 f(X)[\xi,\xi]$ is the second Fréchet derivative applied to $(\xi,\xi)$. The symmetry $f(X)=f(X^\top)$ and the $C^2$ assumption are the paper's standing assumptions (p. 2).
-- source:
--   Luo, Li & Zhang, On Geometric Connections of Embedded and Quotient Geometries in Riemannian Fixed-rank Matrix Optimization, arXiv:2110.12121v2, p. 17, Proposition 1, first bullet (on M^e_{r+}), (19); standing assumptions p. 2

import Mathlib
import Definitions.Def_FixedRankGeom_PSD_Model

open scoped RealInnerProductSpace Matrix ContDiff
open ProjLikeRetr.Retractor

namespace FixedRankGeom.PSD

/-- Proposition 1, first bullet (on `M^e_{r+}`), (19), p. 17. -/
theorem prop_1_emb {p r : ℕ} (hr : 0 < r) (hrp : r ≤ p)
    (f : Mat p p → ℝ) (hf : ContDiff ℝ 2 f) (hfs : ∀ X, f (ofMat (toMat X)ᵀ) = f X)
    (X : Mat p p) (hX : X ∈ psdRankSet p r)
    (U : Matrix (Fin p) (Fin r) ℝ) (Uperp : Matrix (Fin p) (Fin (p - r)) ℝ)
    (hQ : (Matrix.fromCols U Uperp)ᵀ * Matrix.fromCols U Uperp = 1)
    (hUX : U * Uᵀ * toMat X = toMat X) :
    let PU := U * Uᵀ
    let PUperp := Uperp * Uperpᵀ
    let G := toMat (gradient f X)
    let Sig := Uᵀ * toMat X * U
    toMat (ZORiem.RGD.rgrad (psdRankSet p r) f X) = PU * G * PU + PUperp * G * PU + PU * G * PUperp ∧
    (∃ q, IsEmbHessQuad (psdRankSet p r) f X q) ∧
    ∀ q, IsEmbHessQuad (psdRankSet p r) f X q →
      ∀ (S : Matrix (Fin r) (Fin r) ℝ) (D : Matrix (Fin (p - r)) (Fin r) ℝ), Sᵀ = S →
        let ξ := ofMat (Matrix.fromCols U Uperp * Matrix.fromBlocks S Dᵀ D 0 *
          (Matrix.fromCols U Uperp)ᵀ)
        q ξ = iteratedFDeriv ℝ 2 f X ![ξ, ξ] +
          2 * ⟪gradient f X, ofMat (Uperp * D * Sig⁻¹ * Dᵀ * Uperpᵀ)⟫ := by sorry

end FixedRankGeom.PSD
