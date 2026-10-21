-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_RN_EF_inv_mul
-- name    : ExactVacuumAtlas.EinsteinMaxwell.RN.EF.inv_mul
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-21T01:48:57.059503+00:00
-- url     : https://prove2.me/theorems/e98c0169-5f5e-40f2-afa8-5d4da81227c1
-- title:
--   RN inverse is a true inverse
-- statement:
--   RN inverse is a true inverse
--
--   giRN M b · gRN M b = 1 on domRN, every real M, b.
--
--   **Scope.** Exactly the hypotheses printed in the formal statement.
--
--   **中文摘要** RN 逆矩阵检验。
-- source:
--   He Wang, Exact Spacetime Atlas IV: Certified Einstein–Maxwell Backgrounds and First Variations. Local source, no public repository; commit 543904bfcfa3bb169f43fc4d9dbd569999b71886; Atlas/EinsteinMaxwell/RN/EFCert.lean#L61-L67; SHA-256 357f1c6dcc9d4b1de6bc91d8180a4c7e5b75316199ee7ef426a62e658987ab64. Registered definitions and literature: mission/PHYSICS_BOUNDARY.md (§H–§J); Müller–Grave arXiv:0904.4184; Newman et al., J. Math. Phys. 6 (1965) 918.

import Mathlib
import Definitions.Def_Atlas_Core_Basic
import Definitions.Def_Atlas_Core_Certificate
import Definitions.Def_Atlas_Core_Lift
import Definitions.Def_Atlas_EinsteinMaxwell_Basic
import Definitions.Def_Atlas_EinsteinMaxwell_Certificate
import Definitions.Def_Atlas_EinsteinMaxwell_RN_Defs
import Definitions.Def_Atlas_EinsteinMaxwell_RN_Frame
open Real
open scoped ContDiff
open ExactVacuumAtlas ExactVacuumAtlas.EinsteinMaxwell ExactVacuumAtlas.EinsteinMaxwell.RN
open ExactVacuumAtlas
open ExactVacuumAtlas.EinsteinMaxwell
open ExactVacuumAtlas.EinsteinMaxwell.RN
set_option maxHeartbeats 4000000

theorem ExactVacuumAtlas.EinsteinMaxwell.RN.EF.inv_mul (M b : ℝ) {x : Pt 4} (hx : x ∈ domRN) :
    metricMatrix (giRN M b) x * metricMatrix (gRN M b) x = 1 := by sorry
