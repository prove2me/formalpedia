-- Prove2me | Theorems.Thm_ExpConeIPM_Curvature_thirdDeriv_witness_value
-- name    : ExpConeIPM.Curvature.thirdDeriv_witness_value
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T17:07:38.711565+00:00
-- url     : https://prove2.me/theorems/022b5a9a-7e97-4d73-a63f-d0d0d9d0fd6f
-- title:
--   §5, p. 356 — $F'''(\hat x)[\hat u, \hat v, \hat v] = 4$ for $\hat v = (1, 8e^{-2}, 4e^{-2})$
-- statement:
--   Let $F$ be the exponential-cone barrier (2), $\hat x = (1, e^{-2}, 0)$, $\hat u = (1, 0, 0)$ and $\hat v := (1, 8e^{-2}, 4e^{-2})$. Then
--
--   $$
--   F'''(\hat x)[\hat u, \hat v, \hat v] = \bigl\langle F'''(\hat x)[\hat u]\,\hat v, \hat v\bigr\rangle = 4.
--   $$
--
--   Since $\hat x$ is interior to the exponential cone and $\hat u$ lies in the cone, this positive value shows that $F'''(\hat x)[\hat u] \not\preceq 0$.
--
--   **Formalization Note** $F'''(\hat x)[\hat u]$ is `fderiv ℝ (hess barrier) x̂ û`, and the trilinear form is read with $\hat u$ in the differentiation slot; by symmetry of third derivatives any placement gives the same number.
-- source:
--   Dahl, Andersen, A primal-dual interior-point algorithm for nonsymmetric exponential-cone optimization, Math. Program. 194 (2022), p. 356, §5

import Mathlib
import Definitions.Def_ExpConeIPM_Curvature_ExpCone
import Definitions.Def_ExpConeIPM_Curvature_NegativeCurvature

open scoped InnerProductSpace

namespace ExpConeIPM.Curvature

/-- **§5, p. 356 — the value 4.** For `x̂ = (1, e^{−2}, 0)`, `û = (1, 0, 0)` and
`v̂ := (1, 8e^{−2}, 4e^{−2})`, `F'''(x̂)[û, v̂, v̂] = ⟪F'''(x̂)[û] v̂, v̂⟫ = 4`. -/
theorem thirdDeriv_witness_value :
    ⟪thirdDeriv barrier !₂[1, Real.exp (-2), 0] !₂[1, 0, 0]
        !₂[1, 8 * Real.exp (-2), 4 * Real.exp (-2)],
      !₂[1, 8 * Real.exp (-2), 4 * Real.exp (-2)]⟫_ℝ = 4 := by sorry

end ExpConeIPM.Curvature
