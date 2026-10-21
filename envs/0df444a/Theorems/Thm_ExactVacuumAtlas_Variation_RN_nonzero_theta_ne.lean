-- Prove2me | Theorems.Thm_ExactVacuumAtlas_Variation_RN_nonzero_theta_ne
-- name    : ExactVacuumAtlas.Variation.RN.nonzero_theta_ne
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-21T01:50:50.597598+00:00
-- url     : https://prove2.me/theorems/7c19d49f-17c5-459b-be10-f227f67be660
-- title:
--   The same linearised operator is not identically zero: an RN direction with LE_θθ ≠ 0
-- statement:
--   The same linearised operator is not identically zero: an RN direction with LE_θθ ≠ 0
--
--   For all real M, Q and x ∈ domRN: LE_θθ(gRN M (Q²), giRN M (Q²), faradayRN Q; h = tanB, f = 0)(x) ≠ 0, where tanB has the single component h_vv = −1/r² (the b-direction of the RN ansatz at b = Q²).
--
--   **Scope.** This direction is the tangent of the non-solution family b = Q² + ε (cert_iff); it is not a linearised solution. A vanishing first variation elsewhere is never claimed to give a new exact solution.
--
--   **中文摘要** 非零检验：同一 L 在 RN 背景、方向 h_vv=−1/r²、f=0 上 LE_θθ=1/r²≠0。
-- source:
--   He Wang, Exact Spacetime Atlas IV: Certified Einstein–Maxwell Backgrounds and First Variations. Local source, no public repository; commit 543904bfcfa3bb169f43fc4d9dbd569999b71886; Atlas/EinsteinMaxwell/Variation/RN.lean#L172-L175; SHA-256 7513cd6c91a5e550bb62e1cac2f2c8a8c17fa469087ba3c27bf9c1eab933f66f. Registered definitions and literature: mission/PHYSICS_BOUNDARY.md (§H–§J); Müller–Grave arXiv:0904.4184; Newman et al., J. Math. Phys. 6 (1965) 918.

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

theorem ExactVacuumAtlas.Variation.RN.nonzero_theta_ne (M Q : ℝ) {x : Pt 4} (hx : x ∈ domRN) :
    linEinstein (gRN M (Q ^ 2)) (giRN M (Q ^ 2)) (faradayRN Q) tanB 0 2 2 x ≠ 0 := by sorry
