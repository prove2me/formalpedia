-- Prove2me | Theorems.Thm_EulerMascheroni_Hankel_det_le_det_add_smul_posSemidef
-- name    : EulerMascheroni.Hankel.det_le_det_add_smul_posSemidef
-- status  : Open
-- author  : @shivm
-- created : 2026-10-09T09:32:03.883072+00:00
-- url     : https://prove2.me/theorems/1cbf5793-07da-469e-bcfe-01e9899d7927
-- title:
--   A positive-semidefinite perturbation cannot decrease a positive-definite determinant
-- statement:
--   Let $R$ be a real positive-definite $n\times n$ matrix, $S$ positive semidefinite, and $g>0$. Then
--   $$\det R\;\le\;\det(R+gS).$$
--
--   **Proof sketch.** Write $R+gS=R^{1/2}\bigl(I+gR^{-1/2}SR^{-1/2}\bigr)R^{1/2}$. The middle factor is $I$ plus a positive-semidefinite matrix, so each of its eigenvalues is at least $1$ and its determinant is at least $1$; multiplying by $\det R$ gives the claim.
--
--   **Why this matters for Euler's constant.** It obstructs the most natural attempt at `EulerMascheroni.Hankel.gamma_affine_hankel_data`. That node asks for affine Hankel data $(a_{i+j}+b_{i+j}X)$ which is positive definite at $X=\gamma$ and whose determinant is eventually smaller than $e^{-cn^2}$ after clearing denominators. The only ansatz making positive definiteness automatic is $\mu=\nu+\gamma\lambda$ with $\nu,\lambda$ positive measures, giving $R,S$ both positive semidefinite moment matrices. The inequality above then forces $\det(R+\gamma S)\ge\det R$, and since $m\det R$ is a nonzero integer whenever $m$ clears the denominators, the cleared form has absolute value at least $1$ and cannot tend to zero. Hence any solution of that node must use an **indefinite** $\gamma$-part.
-- source:
--   Standard consequence of the congruence R + gS = R^{1/2}(I + g R^{-1/2} S R^{-1/2}) R^{1/2}; recorded as an obstruction for EulerMascheroni.Hankel.gamma_affine_hankel_data.

import Mathlib

theorem EulerMascheroni.Hankel.det_le_det_add_smul_posSemidef {n : ℕ}
    (R S : Matrix (Fin n) (Fin n) ℝ) (hR : R.PosDef) (hS : S.PosSemidef)
    (g : ℝ) (hg : 0 < g) :
    R.det ≤ (R + g • S).det := by
  sorry
