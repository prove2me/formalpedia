-- Prove2me | Theorems.Thm_DSReg_whitening_reduction
-- name    : DSReg.whitening_reduction
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T04:30:42.538398+00:00
-- url     : https://prove2.me/theorems/3e4dbd1b-4725-427d-9721-c4164c7d99f0
-- title:
--   Lemma 4: whitening reduction
-- statement:
--   Let $z\sim N(0,I_d)$ and $h(z)=Az$ for an invertible $A\in\mathbb{R}^{d\times d}$. Then $\operatorname{Cov}(h)=AA^\top$, the matrix
--
--   $$\tilde Q=(AA^\top)^{-1/2}A$$
--
--   is orthogonal, and $W=\operatorname{Cov}(h)^{-1/2}$ satisfies $Wh(z)=\tilde Qz$ for every $z$. Whitening therefore reduces any invertible linear ambiguity to an orthogonal one.
-- source:
--   Zheng, Klindt, Balestriero and Schölkopf, DSReg: Provably Recovering Individual World Latents without Reconstruction, arXiv:2610.09457v1 (2026), Appendix A.4, Lemma 4, p. 21

import Mathlib
import Definitions.Def_DSReg_Basic

open MeasureTheory

namespace DSReg

theorem whitening_reduction {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) (hA : IsUnit A.det) :
    covMat (stdGaussian d) (fun z => A.mulVec z) = A * A.transpose ∧
    invSqrt (A * A.transpose) * A ∈ Matrix.orthogonalGroup (Fin d) ℝ ∧
    ∀ z : Fin d → ℝ, (invSqrt (covMat (stdGaussian d) (fun z => A.mulVec z))).mulVec (A.mulVec z) =
      (invSqrt (A * A.transpose) * A).mulVec z := by sorry

end DSReg
