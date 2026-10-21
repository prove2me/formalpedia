-- Prove2me | Theorems.Thm_ExactVacuumAtlas_Deriv_mul_sin_sq
-- name    : ExactVacuumAtlas.Deriv.mul_sin_sq
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-21T01:43:55.119409+00:00
-- url     : https://prove2.me/theorems/c72ea2bb-011e-4130-b8fc-24207f230d8c
-- title:
--   Derivative of K sin²θ
-- statement:
--   Derivative of K sin²θ
--
--   HasDerivAt (t ↦ K sin²t) (K · 2 sin θ cos θ) at θ.
--
--   **Scope.** Exactly the hypotheses printed in the formal statement.
--
--   **中文摘要** 导数引理 d(K sin²θ)。
-- source:
--   He Wang, Exact Spacetime Atlas IV: Certified Einstein–Maxwell Backgrounds and First Variations. Local source, no public repository; commit 543904bfcfa3bb169f43fc4d9dbd569999b71886; Atlas/Core/Deriv.lean#L66-L70; SHA-256 dc49ec3a0b39ea3e075312c79b8b14e378ffdc0688d2931d08c6421ec4264e95. Registered definitions and literature: mission/PHYSICS_BOUNDARY.md (§H–§J); Müller–Grave arXiv:0904.4184; Newman et al., J. Math. Phys. 6 (1965) 918.

import Mathlib
open Real

theorem ExactVacuumAtlas.Deriv.mul_sin_sq (K θ : ℝ) :
    HasDerivAt (fun t => K * sin t ^ 2) (K * (2 * sin θ * cos θ)) θ := by sorry
