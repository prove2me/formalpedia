-- Prove2me | Theorems.Thm_ExactVacuumAtlas_Variation_RN_nonzero_theta
-- name    : ExactVacuumAtlas.Variation.RN.nonzero_theta
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-21T01:51:03.433838+00:00
-- url     : https://prove2.me/theorems/b83b47e5-5642-48e6-9ec5-0c8a972caa4f
-- title:
--   Value LE_θθ = 1/r² of the RN b-direction
-- statement:
--   Value LE_θθ = 1/r² of the RN b-direction
--
--   For all real M, Q and x ∈ domRN: LE_θθ(gRN M (Q²), giRN M (Q²), faradayRN Q; tanB, 0)(x) = 1/r² (r = x¹).
--
--   **Scope.** Same operator LE as the goal; no test-specific operator.
--
--   **中文摘要** RN b 方向的 LE_θθ 精确值 1/r²。
-- source:
--   He Wang, Exact Spacetime Atlas IV: Certified Einstein–Maxwell Backgrounds and First Variations. Local source, no public repository; commit 543904bfcfa3bb169f43fc4d9dbd569999b71886; Atlas/EinsteinMaxwell/Variation/RN.lean#L156-L170; SHA-256 7513cd6c91a5e550bb62e1cac2f2c8a8c17fa469087ba3c27bf9c1eab933f66f. Registered definitions and literature: mission/PHYSICS_BOUNDARY.md (§H–§J); Müller–Grave arXiv:0904.4184; Newman et al., J. Math. Phys. 6 (1965) 918.

import Mathlib
import Definitions.Def_Atlas_Core_Basic
import Definitions.Def_Atlas_Core_Certificate
import Definitions.Def_Atlas_Core_Lift
import Definitions.Def_Atlas_EinsteinMaxwell_Basic
import Definitions.Def_Atlas_EinsteinMaxwell_Certificate
import Definitions.Def_Atlas_EinsteinMaxwell_RN_Defs
import Definitions.Def_Atlas_EinsteinMaxwell_RN_Frame
import Definitions.Def_Atlas_EinsteinMaxwell_Variation_Defs
import Definitions.Def_Atlas_EinsteinMaxwell_Variation_RN
import Definitions.Def_Atlas_Transport_MatrixCalc
open Real
open scoped ContDiff
open ExactVacuumAtlas.EinsteinMaxwell ExactVacuumAtlas.EinsteinMaxwell.RN

theorem ExactVacuumAtlas.Variation.RN.nonzero_theta (M Q : ℝ) {x : Pt 4} (hx : x ∈ domRN) :
    linEinstein (gRN M (Q ^ 2)) (giRN M (Q ^ 2)) (faradayRN Q) tanB 0 2 2 x = 1 / x 1 ^ 2 := by sorry
