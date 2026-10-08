-- Prove2me | Theorems.Thm_ExpConeIPM_Curvature_thirdDeriv_witness_matrix
-- name    : ExpConeIPM.Curvature.thirdDeriv_witness_matrix
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T17:07:20.012981+00:00
-- url     : https://prove2.me/theorems/bbca8b50-0ade-41e7-9f53-df4285986ecf
-- title:
--   §5, p. 356 — $F'''(\hat x)[\hat u]$ at $\hat x = (1, e^{-2}, 0)$, $\hat u = (1,0,0)$
-- statement:
--   Let $F$ be the exponential-cone barrier (2), $\hat x = (1, e^{-2}, 0)$ and $\hat u = (1, 0, 0)$. Then
--
--   $$
--   F'''(\hat x)[\hat u] = \begin{bmatrix} -4 & e^2/2 & e^2/2 \\ e^2/2 & 0 & 0 \\ e^2/2 & 0 & -e^4/4 \end{bmatrix}.
--   $$
--
--   The matrix is indefinite: its $(1,1)$ entry is negative while, by the companion milestone, its quadratic form is positive at $\hat v = (1, 8e^{-2}, 4e^{-2})$.
--
--   **Formalization Note** $F'''(\hat x)[\hat u]$ is `fderiv ℝ (hess barrier) x̂ û`; the matrix acts on `EuclideanSpace ℝ (Fin 3)` through the standard basis (`Matrix.toEuclideanCLM`), so its $(i,j)$ entry is $\langle F'''(\hat x)[\hat u]e_j, e_i\rangle$.
-- source:
--   Dahl, Andersen, A primal-dual interior-point algorithm for nonsymmetric exponential-cone optimization, Math. Program. 194 (2022), p. 356, §5

import Mathlib
import Definitions.Def_ExpConeIPM_Curvature_ExpCone
import Definitions.Def_ExpConeIPM_Curvature_NegativeCurvature

open scoped InnerProductSpace

namespace ExpConeIPM.Curvature

/-- **§5, p. 356 — the matrix `F'''(x̂)[û]`.** At `x̂ = (1, e^{−2}, 0)` and `û = (1, 0, 0)`,
```
F'''(x̂)[û] = [ −4     e²/2   e²/2  ;
               e²/2    0      0    ;
               e²/2    0    −e⁴/4  ],
```
the matrix acting on `ℝ³` through the standard basis (`Matrix.toEuclideanCLM`). -/
theorem thirdDeriv_witness_matrix :
    thirdDeriv barrier !₂[1, Real.exp (-2), 0] !₂[1, 0, 0] =
      Matrix.toEuclideanCLM (𝕜 := ℝ)
        !![-4, Real.exp 2 / 2, Real.exp 2 / 2;
           Real.exp 2 / 2, 0, 0;
           Real.exp 2 / 2, 0, -Real.exp 4 / 4] := by sorry

end ExpConeIPM.Curvature
