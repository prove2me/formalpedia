-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_KN_closed
-- name    : ExactVacuumAtlas.EinsteinMaxwell.KN.closed
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-21T01:46:06.410135+00:00
-- url     : https://prove2.me/theorems/b489f7a3-8df8-45b8-9d29-afec08fe040b
-- title:
--   KN Faraday residual vanishes
-- statement:
--   KN Faraday residual vanishes
--
--   H_ijk(faradayKN a Q)(x) = 0 for x ∈ domReg M a Q.
--
--   **Scope.** Exactly the hypotheses printed in the formal statement.
--
--   **中文摘要** KN 的 H = 0。
-- source:
--   He Wang, Exact Spacetime Atlas IV: Certified Einstein–Maxwell Backgrounds and First Variations. Local source, no public repository; commit 543904bfcfa3bb169f43fc4d9dbd569999b71886; Atlas/EinsteinMaxwell/KN/Cert.lean#L188-L192; SHA-256 83d8b851ed8987c89596808d4357bed8ec1ac87efc28a406c3573f1bec168e4c. Registered definitions and literature: mission/PHYSICS_BOUNDARY.md (§H–§J); Müller–Grave arXiv:0904.4184; Newman et al., J. Math. Phys. 6 (1965) 918.

import Mathlib
import Definitions.Def_Atlas_Core_Basic
import Definitions.Def_Atlas_Core_Certificate
import Definitions.Def_Atlas_Core_Lift
import Definitions.Def_Atlas_EinsteinMaxwell_Basic
import Definitions.Def_Atlas_EinsteinMaxwell_Certificate
import Definitions.Def_Atlas_EinsteinMaxwell_KN_Defs
import Definitions.Def_Atlas_EinsteinMaxwell_KN_Domain
import Definitions.Def_Atlas_Kerr_Frame
import Definitions.Def_Atlas_Kerr_InAtoms
import Definitions.Def_KerrBL_CoordGeometry
import Definitions.Def_KerrBL_Kerr_Metric
open Real
open scoped ContDiff

theorem ExactVacuumAtlas.EinsteinMaxwell.KN.closed (M a Q : ℝ) {x : Pt 4} (hx : x ∈ domReg M a Q) (i j k : Fin 4) :
    faradayCyclic (faradayKN a Q) i j k x = 0 := by sorry
