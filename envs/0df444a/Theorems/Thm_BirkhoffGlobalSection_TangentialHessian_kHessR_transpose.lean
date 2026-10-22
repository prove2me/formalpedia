-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_TangentialHessian_kHessR_transpose
-- name    : BirkhoffGlobalSection.TangentialHessian.kHessR_transpose
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-29T22:42:46.515795+00:00
-- url     : https://prove2.me/theorems/a1ed1579-ee1a-4aa1-937d-e425b7bb905b
-- title:
--   The Hessian of the Levi-Civita Hamiltonian is symmetric
-- statement:
--   For all $\mu, c, r$ and every phase point $s = (z_1, z_2, w_1, w_2)$, the explicit Hessian of the Levi-Civita regularized Hamiltonian $K_{\mu,c} = P_{\mu,c} - \mu Z/r$, with $r$ treated as a free parameter, is a symmetric matrix.
--
--   This is the symmetry needed to apply the block formula for bordered forms, and to write the tangential Hessian as $F\,\operatorname{Hess}K\,F^{\mathsf T}$ in the quaternion frame.
--
--   **Formalization note.** The Hessian is the definition `kHessR μ c r s`; the statement is `(kHessR μ c r s).transpose = kHessR μ c r s`.
-- source:
--   Joung–van Koert, https://arxiv.org/abs/2407.19159v3, Proposition 4.4, Section 2.

import Definitions.Def_BirkhoffGlobalSection_TangentialHessian

namespace BirkhoffGlobalSection.TangentialHessian

/-- (b) `kHessR` is symmetric. -/
theorem kHessR_transpose (μ c r : ℝ) (s : Phase) : (kHessR μ c r s).transpose = kHessR μ c r s := by sorry

end BirkhoffGlobalSection.TangentialHessian
