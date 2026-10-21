-- Prove2me | Theorems.Thm_ExactVacuumAtlas_RNDeriv_neg_one_sub_div_add_div_sq
-- name    : ExactVacuumAtlas.RNDeriv.neg_one_sub_div_add_div_sq
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-21T01:48:34.341816+00:00
-- url     : https://prove2.me/theorems/d7bd7c80-b83e-4d7d-88bc-a7f40274fdad
-- title:
--   Derivative of −(1 − K/u + L/u²)
-- statement:
--   Derivative of −(1 − K/u + L/u²)
--
--   HasDerivAt (u ↦ −(1 − K/u + L/u²)) (−K/r² + 2L/r³) at r ≠ 0 (the RN g_vv profile).
--
--   **Scope.** Exactly the hypotheses printed in the formal statement.
--
--   **中文摘要** RN g_vv 剖面的导数。
-- source:
--   He Wang, Exact Spacetime Atlas IV: Certified Einstein–Maxwell Backgrounds and First Variations. Local source, no public repository; commit 543904bfcfa3bb169f43fc4d9dbd569999b71886; Atlas/EinsteinMaxwell/RN/Deriv.lean#L13-L21; SHA-256 be20df290bc44eba3b516e6dedbe84a8c4ef45320f639ac84cfcf286cdcdfb5b. Registered definitions and literature: mission/PHYSICS_BOUNDARY.md (§H–§J); Müller–Grave arXiv:0904.4184; Newman et al., J. Math. Phys. 6 (1965) 918.

import Mathlib
open Real

theorem ExactVacuumAtlas.RNDeriv.neg_one_sub_div_add_div_sq (K L r : ℝ) (hr : r ≠ 0) :
    HasDerivAt (fun u => -(1 - K / u + L / u ^ 2)) (-K / r ^ 2 + 2 * L / r ^ 3) r := by sorry
