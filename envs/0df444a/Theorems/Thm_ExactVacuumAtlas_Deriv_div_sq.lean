-- Prove2me | Theorems.Thm_ExactVacuumAtlas_Deriv_div_sq
-- name    : ExactVacuumAtlas.Deriv.div_sq
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-21T01:43:56.074821+00:00
-- url     : https://prove2.me/theorems/862960b1-894b-4f4c-8eea-b3ea500a779c
-- title:
--   Derivative of K/u²
-- statement:
--   Derivative of K/u²
--
--   HasDerivAt (u ↦ K/u²) (−2K/r³) at r ≠ 0.
--
--   **Scope.** Exactly the hypotheses printed in the formal statement.
--
--   **中文摘要** 导数引理 d(K/u²)。
-- source:
--   He Wang, Exact Spacetime Atlas IV: Certified Einstein–Maxwell Backgrounds and First Variations. Local source, no public repository; commit 543904bfcfa3bb169f43fc4d9dbd569999b71886; Atlas/Core/Deriv.lean#L34-L39; SHA-256 dc49ec3a0b39ea3e075312c79b8b14e378ffdc0688d2931d08c6421ec4264e95. Registered definitions and literature: mission/PHYSICS_BOUNDARY.md (§H–§J); Müller–Grave arXiv:0904.4184; Newman et al., J. Math. Phys. 6 (1965) 918.

import Mathlib
open Real

theorem ExactVacuumAtlas.Deriv.div_sq (K r : ℝ) (hr : r ≠ 0) : HasDerivAt (fun u => K / u ^ 2) (-2 * K / r ^ 3) r := by sorry
