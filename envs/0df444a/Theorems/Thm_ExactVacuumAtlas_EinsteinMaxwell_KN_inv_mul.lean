-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_KN_inv_mul
-- name    : ExactVacuumAtlas.EinsteinMaxwell.KN.inv_mul
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-21T01:47:55.668987+00:00
-- url     : https://prove2.me/theorems/35f919a7-5d48-452d-925f-50ea1dcc2939
-- title:
--   KN inverse is a true inverse
-- statement:
--   KN inverse is a true inverse
--
--   giKN · gKN = 1 (4×4 matrices) on domReg M a Q.
--
--   **Scope.** Exactly the hypotheses printed in the formal statement.
--
--   **中文摘要** KN 逆矩阵检验。
-- source:
--   He Wang, Exact Spacetime Atlas IV: Certified Einstein–Maxwell Backgrounds and First Variations. Local source, no public repository; commit 543904bfcfa3bb169f43fc4d9dbd569999b71886; Atlas/EinsteinMaxwell/KN/Cert.lean#L29-L35; SHA-256 83d8b851ed8987c89596808d4357bed8ec1ac87efc28a406c3573f1bec168e4c. Registered definitions and literature: mission/PHYSICS_BOUNDARY.md (§H–§J); Müller–Grave arXiv:0904.4184; Newman et al., J. Math. Phys. 6 (1965) 918.

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

theorem ExactVacuumAtlas.EinsteinMaxwell.KN.inv_mul (M a Q : ℝ) {x : Pt 4} (hx : x ∈ domReg M a Q) :
    metricMatrix (giKN M a Q) x * metricMatrix (gKN M a Q) x = 1 := by sorry
