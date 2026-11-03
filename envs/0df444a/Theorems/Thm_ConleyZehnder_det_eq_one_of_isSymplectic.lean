-- Prove2me | Theorems.Thm_ConleyZehnder_det_eq_one_of_isSymplectic
-- name    : ConleyZehnder.det_eq_one_of_isSymplectic
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-02T16:10:43.825006+00:00
-- url     : https://prove2.me/theorems/d3aeda13-0624-4ed6-a7e3-5ec4771aea5d
-- title:
--   Symplectic 2×2 matrices have determinant one
-- statement:
--   Let $A$ be a real $2\times2$ matrix with $AJ_0A^{T}=J_0$, where $J_0=\begin{pmatrix}0&-1\\1&0\end{pmatrix}$. Then $\det A=1$.
--
--   This is the basic identity $\mathrm{Sp}(2)=\mathrm{SL}(2,\mathbb{R})$ in the conventions of the Conley–Zehnder setting.
--
--   **Formalization Note** $A$ is `ConleyZehnder.Mat 1` (rows and columns indexed by `Fin 1 ⊕ Fin 1`), and the symplectic condition is `ConleyZehnder.IsSymplectic`.
-- source:
--   J. Gutt, Generalized Conley–Zehnder index, Ann. Fac. Sci. Toulouse Math. 23 (2014), arXiv:1307.7239, Section 2 (auxiliary lemma)

import Definitions.Def_ConleyZehnder_Setting

namespace ConleyZehnder

/-- A symplectic `2 × 2` matrix has determinant `1`. -/
theorem det_eq_one_of_isSymplectic (A : Mat 1) (hA : IsSymplectic A) : A.det = 1 := by
  sorry

end ConleyZehnder
