-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_RN_EF_einstein_zero_at_iff
-- name    : ExactVacuumAtlas.EinsteinMaxwell.RN.EF.einstein_zero_at_iff
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-21T01:49:08.34747+00:00
-- url     : https://prove2.me/theorems/8bc95e41-8093-4dc5-9101-ea56fabc6875
-- title:
--   RN pointwise matching
-- statement:
--   RN pointwise matching
--
--   At any x ∈ domRN: all E_ab(gRN M b, giRN M b, faradayRN Q)(x) = 0 ⟺ b = Q².
--
--   **Scope.** Exactly the hypotheses printed in the formal statement.
--
--   **中文摘要** RN 逐点匹配：E(x)=0 ⟺ b=Q²。
-- source:
--   He Wang, Exact Spacetime Atlas IV: Certified Einstein–Maxwell Backgrounds and First Variations. Local source, no public repository; commit 543904bfcfa3bb169f43fc4d9dbd569999b71886; Atlas/EinsteinMaxwell/RN/EFCert.lean#L156-L167; SHA-256 357f1c6dcc9d4b1de6bc91d8180a4c7e5b75316199ee7ef426a62e658987ab64. Registered definitions and literature: mission/PHYSICS_BOUNDARY.md (§H–§J); Müller–Grave arXiv:0904.4184; Newman et al., J. Math. Phys. 6 (1965) 918.

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

theorem ExactVacuumAtlas.EinsteinMaxwell.RN.EF.einstein_zero_at_iff (M b Q : ℝ) {x : Pt 4} (hx : x ∈ domRN) :
    (∀ i j, einsteinMaxwell (gRN M b) (giRN M b) (faradayRN Q) i j x = 0) ↔ b = Q ^ 2 := by sorry
