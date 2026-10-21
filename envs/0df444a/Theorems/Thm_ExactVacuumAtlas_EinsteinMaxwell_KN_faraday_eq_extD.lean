-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_KN_faraday_eq_extD
-- name    : ExactVacuumAtlas.EinsteinMaxwell.KN.faraday_eq_extD
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-21T01:46:25.546767+00:00
-- url     : https://prove2.me/theorems/7e3581fd-accd-4d02-8b62-14ce1579681f
-- title:
--   KN field is dA
-- statement:
--   KN field is dA
--
--   On domReg M a Q: faradayKN a Q = extD (emPotentialKN a Q) componentwise.
--
--   **Scope.** Exactly the hypotheses printed in the formal statement.
--
--   **中文摘要** KN 场等于势的外微分。
-- source:
--   He Wang, Exact Spacetime Atlas IV: Certified Einstein–Maxwell Backgrounds and First Variations. Local source, no public repository; commit 543904bfcfa3bb169f43fc4d9dbd569999b71886; Atlas/EinsteinMaxwell/KN/Cert.lean#L181-L186; SHA-256 83d8b851ed8987c89596808d4357bed8ec1ac87efc28a406c3573f1bec168e4c. Registered definitions and literature: mission/PHYSICS_BOUNDARY.md (§H–§J); Müller–Grave arXiv:0904.4184; Newman et al., J. Math. Phys. 6 (1965) 918.

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

theorem ExactVacuumAtlas.EinsteinMaxwell.KN.faraday_eq_extD (M a Q : ℝ) {x : Pt 4} (hx : x ∈ domReg M a Q) (i j : Fin 4) :
    faradayKN a Q i j x = extD (emPotentialKN a Q) i j x := by sorry
