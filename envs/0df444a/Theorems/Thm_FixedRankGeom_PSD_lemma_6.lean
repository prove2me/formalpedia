-- Prove2me | Theorems.Thm_FixedRankGeom_PSD_lemma_6
-- name    : FixedRankGeom.PSD.lemma_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:37:30.279728+00:00
-- url     : https://prove2.me/theorems/8a204a1e-b0d0-48be-922a-b6bfb3db05f8
-- title:
--   Lemma 6, pp. 13–14 (full-rank and polar factorizations)
-- statement:
--   Let $0<r\le p$ and let $\mathbb O_r$ be the group of $r\times r$ orthogonal matrices.
--
--   1. For $Y_1,Y_2\in\mathbb R_*^{p\times r}$ (full column rank),
--   $$Y_1Y_1^\top=Y_2Y_2^\top\iff Y_2=Y_1O\ \text{for some } O\in\mathbb O_r .$$
--   2. For $U_1,U_2\in\mathrm{St}(r,p)$ (i.e. $U_i^\top U_i=I_r$) and $B_1,B_2\in\mathbb S_+(r)$ (symmetric positive definite),
--   $$U_1B_1U_1^\top=U_2B_2U_2^\top\iff U_2=U_1O\ \text{and}\ B_2=O^\top B_1O\ \text{for some } O\in\mathbb O_r .$$
--   3. The rank-$r$ PSD matrices are exactly the Gram matrices of full-column-rank factors, and exactly the products $UBU^\top$:
--   $$\mathcal M_{r+}=\{YY^\top: Y\in\mathbb R_*^{p\times r}\}=\{UBU^\top: U\in\mathrm{St}(r,p),\ B\in\mathbb S_+(r)\}.$$
--
--   This is what makes $\mathbb R_*^{p\times r}/\mathbb O_r$ a faithful parametrisation of $\mathcal M_{r+}$: the fibers of $Y\mapsto YY^\top$ are exactly the orbits $[Y]=\{YO\}$; the polar bullet does the same for the second quotient $(\mathrm{St}(r,p)\times\mathbb S_+(r))/\mathbb O_r$.
--
--   **Formalization Note** $\mathbb S_+(r)$ is `Matrix.PosDef` (which includes symmetry); $\mathbb O_r$ is `Matrix.orthogonalGroup`.
-- source:
--   Luo, Li & Zhang, On Geometric Connections of Embedded and Quotient Geometries in Riemannian Fixed-rank Matrix Optimization, arXiv:2110.12121v2, pp. 13–14, Lemma 6

import Mathlib
import Definitions.Def_FixedRankGeom_PSD_Model

open scoped RealInnerProductSpace Matrix ContDiff
open ProjLikeRetr.Retractor

namespace FixedRankGeom.PSD

/-- Lemma 6, pp. 13–14: the full-rank and polar factorizations of rank-`r` PSD matrices. -/
theorem lemma_6 {p r : ℕ} (hr : 0 < r) (hrp : r ≤ p) :
    (∀ Y₁ ∈ fullRankSet p r, ∀ Y₂ ∈ fullRankSet p r,
      (toMat Y₁ * (toMat Y₁)ᵀ = toMat Y₂ * (toMat Y₂)ᵀ ↔
        ∃ O ∈ Matrix.orthogonalGroup (Fin r) ℝ, toMat Y₂ = toMat Y₁ * O)) ∧
    (∀ (U₁ U₂ : Matrix (Fin p) (Fin r) ℝ) (B₁ B₂ : Matrix (Fin r) (Fin r) ℝ),
      U₁ᵀ * U₁ = 1 → U₂ᵀ * U₂ = 1 → B₁.PosDef → B₂.PosDef →
      (U₁ * B₁ * U₁ᵀ = U₂ * B₂ * U₂ᵀ ↔
        ∃ O ∈ Matrix.orthogonalGroup (Fin r) ℝ, U₂ = U₁ * O ∧ B₂ = Oᵀ * B₁ * O)) ∧
    psdRankSet p r = gram '' fullRankSet p r ∧
    psdRankSet p r = {X | ∃ (U : Matrix (Fin p) (Fin r) ℝ) (B : Matrix (Fin r) (Fin r) ℝ),
      Uᵀ * U = 1 ∧ B.PosDef ∧ toMat X = U * B * Uᵀ} := by sorry

end FixedRankGeom.PSD
