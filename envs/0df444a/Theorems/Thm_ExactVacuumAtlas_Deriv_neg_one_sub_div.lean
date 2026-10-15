-- Prove2me | Theorems.Thm_ExactVacuumAtlas_Deriv_neg_one_sub_div
-- name    : ExactVacuumAtlas.Deriv.neg_one_sub_div
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-13T10:07:04.875885+00:00
-- url     : https://prove2.me/theorems/f480a85e-3da7-4514-8a6f-8b40ccf94cd6
-- title:
--   Derivative of $-(1-K/u)$ at a nonzero point
-- statement:
--   Let $K,r$ be real numbers with $r\neq0$. The function $u\mapsto-(1-K/u)$ has, at $u=r$, the derivative $$\frac{d}{du}\Big(-\big(1-\tfrac{K}{u}\big)\Big)\Big|_{u=r}=-\frac{K}{r^2}.$$
--
--   The radial derivative of the coefficient $g_{tt}=-(1-2M/r)$ shared by the standard Schwarzschild and Eddington–Finkelstein metrics ($K=2M$).
--
--   **Formalization Note** Stated with Mathlib's `HasDerivAt`.
-- source:
--   elementary one-variable calculus (standard); Lean source: repository ExactVacuumAtlas (private repository, not publicly accessible; GitHub remote pending (no GitHub identity on the build server)), commit 35f26e6a22f5d72380094fa94edc72dea667df53, Atlas/Core/Deriv.lean#L21-L27 (module Atlas.Core.Deriv, file sha256 dc49ec3a0b39ea3e075312c79b8b14e378ffdc0688d2931d08c6421ec4264e95; uploaded stub = platform_mirror/Theorems/Thm_ExactVacuumAtlas_Deriv_neg_one_sub_div.lean)

import Mathlib
open Real

theorem ExactVacuumAtlas.Deriv.neg_one_sub_div (K r : ℝ) (hr : r ≠ 0) :
    HasDerivAt (fun u => -(1 - K / u)) (-K / r ^ 2) r := by sorry
