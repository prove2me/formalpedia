-- Prove2me | Theorems.Thm_ExactVacuumAtlas_Deriv_div_sq_add_div_cube
-- name    : ExactVacuumAtlas.Deriv.div_sq_add_div_cube
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-13T10:06:23.515845+00:00
-- url     : https://prove2.me/theorems/7b454943-1045-4c95-9474-8ac53c59eff2
-- title:
--   Derivative of $K/u^2+L/u^3$ at a nonzero point
-- statement:
--   Let $K,L,r$ be real numbers with $r\neq0$. The function $u\mapsto K/u^2+L/u^3$ has, at $u=r$, the derivative $$\frac{d}{du}\Big(\frac{K}{u^2}+\frac{L}{u^3}\Big)\Big|_{u=r}=-\frac{2K}{r^3}-\frac{3L}{r^4}.$$
--
--   Elementary derivative rule shared by the Schwarzschild and Eddington–Finkelstein tables, where the coefficients of the Christoffel symbols are rational functions of $r$.
--
--   **Formalization Note** Stated with Mathlib's `HasDerivAt` (an actual derivative, not a default value); division by $u$ is Mathlib's total real division, harmless because $r\neq0$.
-- source:
--   elementary one-variable calculus (standard); Lean source: repository ExactVacuumAtlas (private repository, not publicly accessible; GitHub remote pending (no GitHub identity on the build server)), commit 35f26e6a22f5d72380094fa94edc72dea667df53, Atlas/Core/Deriv.lean#L41-L49 (module Atlas.Core.Deriv, file sha256 dc49ec3a0b39ea3e075312c79b8b14e378ffdc0688d2931d08c6421ec4264e95; uploaded stub = platform_mirror/Theorems/Thm_ExactVacuumAtlas_Deriv_div_sq_add_div_cube.lean)

import Mathlib
open Real

theorem ExactVacuumAtlas.Deriv.div_sq_add_div_cube (K L r : ℝ) (hr : r ≠ 0) :
    HasDerivAt (fun u => K / u ^ 2 + L / u ^ 3) (-2 * K / r ^ 3 - 3 * L / r ^ 4) r := by sorry
