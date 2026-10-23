-- Prove2me | Theorems.Thm_FixedRankGeom_PSD_lemma_3
-- name    : FixedRankGeom.PSD.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:37:36.202368+00:00
-- url     : https://prove2.me/theorems/159043f4-b0b4-4837-963b-af56134b4254
-- title:
--   Lemma 3, p. 11 — M^e_{r+} is a smooth embedded submanifold of dimension pr − r(r−1)/2 with tangent space (14)
-- statement:
--   Let $0<r\le p$, let $X\in\mathcal M_{r+}$ be a rank-$r$ PSD matrix, and let $[U\ U_\perp]$ be a $p\times p$ orthogonal matrix whose first block $U\in\mathrm{St}(r,p)$ spans the top $r$ eigenspace of $X$ (encoded as $UU^\top X=X$). Then $\mathcal M^e_{r+}$ is a smooth embedded submanifold of $\mathbb R^{p\times p}$ of dimension $pr-r(r-1)/2$, and the tangent space of $\mathcal M^e_{r+}$ at $X$ is
--   $$T_X\mathcal M^e_{r+}=\left\{[U\ U_\perp]\begin{bmatrix}S&D^\top\\ D&0\end{bmatrix}[U\ U_\perp]^\top : S\in\mathbb S^{r\times r},\ D\in\mathbb R^{(p-r)\times r}\right\},\qquad(14)$$
--   and its dimension is $pr-r(r-1)/2$.
--
--   This is the explicit description of the embedded tangent space on which the formula (19) for the embedded gradient and Hessian, and the bijection of Proposition 2, are built.
--
--   **Formalization Note** The tangent space is the span of Mathlib's tangent cone (a published definition), not the formula (14), so (14) is a genuine claim. "Smooth embedded submanifold of dimension $d$" is the published coordinate-slice predicate `ProjLikeRetr.Retractor.IsSubmanifold k d` required for every $k\in\mathbb N$. The half of Lemma 3 about $\mathcal M^e_r$ and (15) is not part of this item. For a rank-$r$ PSD matrix the top $r$ eigenspace is the column space, so "$U$ spans the top $r$ eigenspace" is $U^\top U=I_r$ (implied by orthogonality of $[U\ U_\perp]$) together with $UU^\top X=X$. In $\mathbb N$, $r(r-1)$ is even and $pr\ge r(r-1)/2$, so the subtraction and division are exact.
-- source:
--   Luo, Li & Zhang, On Geometric Connections of Embedded and Quotient Geometries in Riemannian Fixed-rank Matrix Optimization, arXiv:2110.12121v2, p. 11, Lemma 3 (PSD half), (14)

import Mathlib
import Definitions.Def_FixedRankGeom_PSD_Model
import Definitions.Def_ProjLikeRetr_Retractor_IsSubmanifold

open scoped RealInnerProductSpace Matrix ContDiff
open ProjLikeRetr.Retractor

namespace FixedRankGeom.PSD

/-- Lemma 3, PSD half, p. 11: `M^e_{r+}` is a smooth (`C^k` for every `k`) embedded submanifold of
`ℝ^{p×p}` of dimension `pr − r(r − 1)/2`, and its tangent space at `X` is (14). -/
theorem lemma_3 {p r : ℕ} (hr : 0 < r) (hrp : r ≤ p)
    (X : Mat p p) (hX : X ∈ psdRankSet p r)
    (U : Matrix (Fin p) (Fin r) ℝ) (Uperp : Matrix (Fin p) (Fin (p - r)) ℝ)
    (hQ : (Matrix.fromCols U Uperp)ᵀ * Matrix.fromCols U Uperp = 1)
    (hUX : U * Uᵀ * toMat X = toMat X) :
    (∀ k : ℕ, IsSubmanifold k (p * r - r * (r - 1) / 2) (psdRankSet p r)) ∧
    (tangentSpace (psdRankSet p r) X : Set (Mat p p)) =
      {ξ | ∃ (S : Matrix (Fin r) (Fin r) ℝ) (D : Matrix (Fin (p - r)) (Fin r) ℝ), Sᵀ = S ∧
        toMat ξ = Matrix.fromCols U Uperp * Matrix.fromBlocks S Dᵀ D 0 * (Matrix.fromCols U Uperp)ᵀ} ∧
    Module.finrank ℝ (tangentSpace (psdRankSet p r) X) = p * r - r * (r - 1) / 2 := by sorry

end FixedRankGeom.PSD
