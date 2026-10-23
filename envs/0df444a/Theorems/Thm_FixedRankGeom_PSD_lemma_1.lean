-- Prove2me | Theorems.Thm_FixedRankGeom_PSD_lemma_1
-- name    : FixedRankGeom.PSD.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:37:36.020739+00:00
-- url     : https://prove2.me/theorems/b550731f-dd90-4e99-aab0-fcbe8e8cbf32
-- title:
--   Lemma 1, p. 7 (canonical horizontal space), on M̄^{q1}_{r+}: the lifted quotient gradient is grad h̄(Y)
-- statement:
--   Let $0<r\le p$, $Y\in\mathbb R_*^{p\times r}$, and let $W_Y$ be symmetric positive definite, giving the metric $\bar g_Y(\eta,\theta)=\operatorname{tr}(W_Y\eta^\top\theta)$. Let $\bar h:\mathbb R^{p\times r}\to\mathbb R$ be differentiable at $Y$ and invariant along the fibers, i.e. $\bar h(ZO)=\bar h(Z)$ for every $Z\in\mathbb R_*^{p\times r}$ and $O\in\mathbb O_r$. Take the canonical horizontal space $\mathcal H_Y$, the $\bar g_Y$-orthogonal complement of the vertical space $\mathcal V_Y=\{Y\Omega:\Omega=-\Omega^\top\}$. Then the Riemannian gradient $\operatorname{grad}\bar h(Y)=\nabla\bar h(Y)W_Y^{-1}$ is horizontal, and therefore the horizontal lift of the quotient gradient equals it:
--   $$\overline{\operatorname{grad} h([Y])}=P^{\mathcal H}_Y\big(\operatorname{grad}\bar h(Y)\big)=\operatorname{grad}\bar h(Y).$$
--
--   This is the abstract Lemma 1 of the paper specialised to the total space $\mathbb R_*^{p\times r}$ of the full-rank factorization quotient; it lets the quotient gradient be computed without any projection.
--
--   **Formalization Note** The horizontal projection $P^{\mathcal H}_Y$ is the component in $\mathcal V_Y\oplus\mathcal H_Y$ (chosen by `Classical.epsilon` in the definition), so the second conclusion includes the uniqueness of that decomposition.
-- source:
--   Luo, Li & Zhang, On Geometric Connections of Embedded and Quotient Geometries in Riemannian Fixed-rank Matrix Optimization, arXiv:2110.12121v2, p. 7, Lemma 1 and (4), applied to M̄^{q1}_{r+} (§4.2.1, p. 12)

import Mathlib
import Definitions.Def_FixedRankGeom_PSD_Model

open scoped RealInnerProductSpace Matrix ContDiff
open ProjLikeRetr.Retractor

namespace FixedRankGeom.PSD

/-- Lemma 1, p. 7, on the total space `ℝ_*^{p×r}` of `M^{q1}_{r+}`: with the canonical horizontal space,
the horizontal lift of `grad h([Y])` is `grad h̄(Y)`. -/
theorem lemma_1 {p r : ℕ} (hr : 0 < r) (hrp : r ≤ p)
    (W : Mat p r → Mat r r) (Y : Mat p r) (hY : Y ∈ fullRankSet p r)
    (hW : (toMat (W Y)).PosDef)
    (hbar : Mat p r → ℝ)
    (hinv : ∀ Z ∈ fullRankSet p r, ∀ O ∈ Matrix.orthogonalGroup (Fin r) ℝ,
      hbar (ofMat (toMat Z * O)) = hbar Z)
    (hd : DifferentiableAt ℝ hbar Y) :
    totalGrad W hbar Y ∈ horizontalSpace W Y ∧ quotGrad W hbar Y = totalGrad W hbar Y := by sorry

end FixedRankGeom.PSD
