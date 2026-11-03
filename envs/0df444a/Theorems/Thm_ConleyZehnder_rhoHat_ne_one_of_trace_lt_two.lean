-- Prove2me | Theorems.Thm_ConleyZehnder_rhoHat_ne_one_of_trace_lt_two
-- name    : ConleyZehnder.rhoHat_ne_one_of_trace_lt_two
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-02T16:10:45.578397+00:00
-- url     : https://prove2.me/theorems/a22384af-20b6-43de-a1d5-c1ff93c4215f
-- title:
--   The normalized complex determinant of a symplectic 2×2 matrix with trace below two is not one
-- statement:
--   Let $A\in\mathrm{Sp}(2)$ with $\operatorname{tr}A<2$. Then $\hat\rho(A)\neq1$, where $\hat\rho(A)=\det_{\mathbb C}C_A/|\det_{\mathbb C}C_A|$ is the normalized complex determinant of the complex-linear part $C_A=\tfrac12(A-J_0AJ_0)$.
--
--   So along a path of symplectic matrices with trace less than $2$, a continuous argument of $\hat\rho$ never meets $2\pi\mathbb{Z}$.
--
--   **Formalization Note** $A$ is `ConleyZehnder.Mat 1` with `ConleyZehnder.IsSymplectic A`, and $\hat\rho$ is `ConleyZehnder.rhoHat`.
-- source:
--   J. Gutt, Generalized Conley–Zehnder index, Ann. Fac. Sci. Toulouse Math. 23 (2014), arXiv:1307.7239, Section 2 (auxiliary lemma)

import Definitions.Def_ConleyZehnder_Setting

namespace ConleyZehnder

/-- For a symplectic `2 × 2` matrix with trace less than `2`, `ρ̂ ≠ 1`. -/
theorem rhoHat_ne_one_of_trace_lt_two (A : Mat 1) (hA : IsSymplectic A) (htr : A.trace < 2) :
    rhoHat A ≠ 1 := by
  sorry

end ConleyZehnder
