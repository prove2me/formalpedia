-- Prove2me | Theorems.Thm_FixedRankGeom_PSD_lemma_4_i
-- name    : FixedRankGeom.PSD.lemma_4_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:37:42.423404+00:00
-- url     : https://prove2.me/theorems/6c0088d7-6ed0-4bee-8f47-50471ea4288f
-- title:
--   Lemma 4 (i), p. 13 — vertical and horizontal spaces of T_Y M̄^{q1}_{r+} and their dimensions
-- statement:
--   Let $0<r\le p$, $Y\in\mathbb R_*^{p\times r}$, and let the weight $W_Y$ be symmetric positive definite, so that $\bar g_Y(\eta,\theta)=\operatorname{tr}(W_Y\eta^\top\theta)$ is an inner product on $\mathbb R^{p\times r}$. Let $[U\ U_\perp]$ be a $p\times p$ orthogonal matrix with $U\in\mathrm{St}(r,p)$ spanning the top $r$ eigenspace of $YY^\top$ (encoded as $UU^\top Y=Y$), and put $P=U^\top Y$. Then
--
--   1. $\mathcal V_Y\bar{\mathcal M}^{q_1}_{r+}=\{U\Omega P^{-\top}: \Omega=-\Omega^\top\in\mathbb R^{r\times r}\}$;
--   2. $\mathcal H_Y\bar{\mathcal M}^{q_1}_{r+}=\{(US+U_\perp D)P^{-\top}: SP^{-\top}W_YP^{-1}\in\mathbb S^{r\times r},\ D\in\mathbb R^{(p-r)\times r}\}$;
--   3. $\dim\mathcal V_Y\bar{\mathcal M}^{q_1}_{r+}=(r^2-r)/2$ and $\dim\mathcal H_Y\bar{\mathcal M}^{q_1}_{r+}=pr-(r^2-r)/2$;
--   4. $\mathcal V_Y\bar{\mathcal M}^{q_1}_{r+}\perp\mathcal H_Y\bar{\mathcal M}^{q_1}_{r+}$ with respect to $\bar g_Y$.
--
--   Here $\mathcal V_Y=\{Y\Omega:\Omega=-\Omega^\top\}$ is the tangent space of the fiber $[Y]$ and $\mathcal H_Y$ is its $\bar g_Y$-orthogonal complement.
--
--   The explicit horizontal space is what Proposition 2 maps bijectively onto the embedded tangent space, and its dimension is the eigenvalue count of Theorem 3.
--
--   **Formalization Note** Since $\mathcal V_Y$ is defined by its first description and $\mathcal H_Y$ as the $\bar g_Y$-orthogonal complement, items 1 (second description), 2 and 3 carry the content and item 4 holds by construction. $U_\perp D$ with $D$ arbitrary is written with the given complement $U_\perp$. In $\mathbb N$, $r^2\ge r$, $r^2-r$ is even and $pr\ge(r^2-r)/2$, so the arithmetic is exact.
-- source:
--   Luo, Li & Zhang, On Geometric Connections of Embedded and Quotient Geometries in Riemannian Fixed-rank Matrix Optimization, arXiv:2110.12121v2, p. 13, Lemma 4 (i)

import Mathlib
import Definitions.Def_FixedRankGeom_PSD_Model

open scoped RealInnerProductSpace Matrix ContDiff
open ProjLikeRetr.Retractor

namespace FixedRankGeom.PSD

/-- Lemma 4 (i), p. 13: vertical and horizontal spaces of `T_Y M̄^{q1}_{r+}`, their dimensions and
their `ḡ_Y`-orthogonality. -/
theorem lemma_4_i {p r : ℕ} (hr : 0 < r) (hrp : r ≤ p)
    (W : Mat p r → Mat r r) (Y : Mat p r) (hY : Y ∈ fullRankSet p r)
    (hW : (toMat (W Y)).PosDef)
    (U : Matrix (Fin p) (Fin r) ℝ) (Uperp : Matrix (Fin p) (Fin (p - r)) ℝ)
    (hQ : (Matrix.fromCols U Uperp)ᵀ * Matrix.fromCols U Uperp = 1)
    (hUY : U * Uᵀ * toMat Y = toMat Y) :
    let P := Uᵀ * toMat Y
    (verticalSpace Y : Set (Mat p r)) =
      {θ | ∃ Ω : Matrix (Fin r) (Fin r) ℝ, Ω = -Ωᵀ ∧ toMat θ = U * Ω * (P⁻¹)ᵀ} ∧
    (horizontalSpace W Y : Set (Mat p r)) =
      {θ | ∃ (S : Matrix (Fin r) (Fin r) ℝ) (D : Matrix (Fin (p - r)) (Fin r) ℝ),
        (S * (P⁻¹)ᵀ * toMat (W Y) * P⁻¹)ᵀ = S * (P⁻¹)ᵀ * toMat (W Y) * P⁻¹ ∧
        toMat θ = (U * S + Uperp * D) * (P⁻¹)ᵀ} ∧
    Module.finrank ℝ (verticalSpace Y) = (r ^ 2 - r) / 2 ∧
    Module.finrank ℝ (horizontalSpace W Y) = p * r - (r ^ 2 - r) / 2 ∧
    (∀ v ∈ verticalSpace Y, ∀ h ∈ horizontalSpace W Y, qmetric W Y v h = 0) := by sorry

end FixedRankGeom.PSD
