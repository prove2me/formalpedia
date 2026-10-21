-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_RN_EF_faraday_eq_extD
-- name    : ExactVacuumAtlas.EinsteinMaxwell.RN.EF.faraday_eq_extD
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-21T01:49:09.137983+00:00
-- url     : https://prove2.me/theorems/0f920c7f-26a5-42fd-9865-bfd3f8a2799c
-- title:
--   RN field is dA
-- statement:
--   RN field is dA
--
--   On domRN: faradayRN Q = extD (emPotentialRN Q).
--
--   **Scope.** Exactly the hypotheses printed in the formal statement.
--
--   **中文摘要** RN 场等于势的外微分。
-- source:
--   He Wang, Exact Spacetime Atlas IV: Certified Einstein–Maxwell Backgrounds and First Variations. Local source, no public repository; commit 543904bfcfa3bb169f43fc4d9dbd569999b71886; Atlas/EinsteinMaxwell/RN/EFCert.lean#L107-L112; SHA-256 357f1c6dcc9d4b1de6bc91d8180a4c7e5b75316199ee7ef426a62e658987ab64. Registered definitions and literature: mission/PHYSICS_BOUNDARY.md (§H–§J); Müller–Grave arXiv:0904.4184; Newman et al., J. Math. Phys. 6 (1965) 918.

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

theorem ExactVacuumAtlas.EinsteinMaxwell.RN.EF.faraday_eq_extD (Q : ℝ) {x : Pt 4} (hx : x ∈ domRN) (i j : Fin 4) :
    faradayRN Q i j x = extD (emPotentialRN Q) i j x := by sorry
