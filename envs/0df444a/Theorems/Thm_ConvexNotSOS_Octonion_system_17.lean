-- Prove2me | Theorems.Thm_ConvexNotSOS_Octonion_system_17
-- name    : ConvexNotSOS.Octonion.system_17
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:15:32.489213+00:00
-- url     : https://prove2.me/theorems/9f709a1a-baa3-4979-b5ff-0df294180822
-- title:
--   Proof of Theorem 4.11 — the k = 17 coefficient system
-- statement:
--   For every $k\ge16$, at the three matrices $X_1,X_2,X_3\in\mathbb R^{16\times k}$ of the proof ($X_1$ has a single $1$ in position $(1,1)$; $X_2=\begin{bmatrix}I_8&0\\I_8&0\end{bmatrix}$; $X_3=\begin{bmatrix}I_{16}&0\end{bmatrix}$), the octonionic quartic has values $q^{\mathbb O}_k(X_1)=1/4$, $q^{\mathbb O}_k(X_2)=64$, $q^{\mathbb O}_k(X_3)=128$. For $k=17$, the values of the eight $s_{ij}$ in the column order of $\Lambda$ form the matrix
--
--   $$\begin{bmatrix}1/272&1/272&14/272&1/17&1/17&14/17&0&0\\16/17&16/17&0&18/17&18/17&140&56&56\\16/17&0&0&1/17&9&126&36&84\end{bmatrix}.$$
--
--   The proof's finite characterization says $q^{\mathbb O}_{17}$ is SOS exactly when these three rows, multiplied by some nonnegative eight-vector, equal $(1/4,64,128)^\top$. The computed system is the certificate-bearing step in the threshold theorem.
--
--   **Formalization Note.** The statement includes the 24 evaluations and the SOS-versus-three-equations equivalence; it does not silently replace the full polynomial condition by evaluation at three arbitrary points.
-- source:
--   Saunderson, A convex form that is not a sum of squares, arXiv:2105.08432v2, p. 14, proof of Theorem 4.11, (14) and 3×8 coefficient matrix

import Definitions.Def_ConvexNotSOS_Octonion_Symmetry

namespace ConvexNotSOS.Octonion
open MvPolynomial

/-- The three evaluation rows and finite feasibility system in the proof of Theorem 4.11. -/
theorem system_17 :
    (∀ k : ℕ, 16 ≤ k →
      evalM (X1 k) (qPoly k) = 1 / 4 ∧
      evalM (X2 k) (qPoly k) = 64 ∧
      evalM (X3 k) (qPoly k) = 128) ∧
    (∀ l : Lam,
      (evalM (X1 17) (sPoly 17 l),
       evalM (X2 17) (sPoly 17 l),
       evalM (X3 17) (sPoly 17 l)) =
        match l with
        | .l00 => ((1 / 272 : ℝ), 16 / 17, 16 / 17)
        | .l10 => ((1 / 272 : ℝ), 16 / 17, 0)
        | .l40 => ((14 / 272 : ℝ), 0, 0)
        | .l01 => ((1 / 17 : ℝ), 18 / 17, 1 / 17)
        | .l11 => ((1 / 17 : ℝ), 18 / 17, 9)
        | .l41 => ((14 / 17 : ℝ), 140, 126)
        | .l2m => ((0 : ℝ), 56, 36)
        | .l3m => ((0 : ℝ), 56, 84)) ∧
    (IsSumSq (qPoly 17) ↔ ∃ coeff : Lam → ℝ,
      (∀ l, 0 ≤ coeff l) ∧
      evalM (X1 17) (qPoly 17) = ∑ l, coeff l * evalM (X1 17) (sPoly 17 l) ∧
      evalM (X2 17) (qPoly 17) = ∑ l, coeff l * evalM (X2 17) (sPoly 17 l) ∧
      evalM (X3 17) (qPoly 17) = ∑ l, coeff l * evalM (X3 17) (sPoly 17 l)) := by sorry

end ConvexNotSOS.Octonion
