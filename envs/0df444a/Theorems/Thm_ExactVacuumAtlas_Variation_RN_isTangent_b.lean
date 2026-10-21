-- Prove2me | Theorems.Thm_ExactVacuumAtlas_Variation_RN_isTangent_b
-- name    : ExactVacuumAtlas.Variation.RN.isTangent_b
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-21T01:51:03.779553+00:00
-- url     : https://prove2.me/theorems/1bfbd3eb-3fe0-41c1-92bf-2dbae8060fa9
-- title:
--   Tangent of the RN b-family
-- statement:
--   Tangent of the RN b-family
--
--   IsTangent of the b-family with h = tanB (h_vv = −1/r²), f = 0.
--
--   **Scope.** Exactly the hypotheses printed in the formal statement.
--
--   **中文摘要** RN b 族的切向 tanB。
-- source:
--   He Wang, Exact Spacetime Atlas IV: Certified Einstein–Maxwell Backgrounds and First Variations. Local source, no public repository; commit 543904bfcfa3bb169f43fc4d9dbd569999b71886; Atlas/EinsteinMaxwell/Variation/RN.lean#L118-L129; SHA-256 7513cd6c91a5e550bb62e1cac2f2c8a8c17fa469087ba3c27bf9c1eab933f66f. Registered definitions and literature: mission/PHYSICS_BOUNDARY.md (§H–§J); Müller–Grave arXiv:0904.4184; Newman et al., J. Math. Phys. 6 (1965) 918.

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

theorem ExactVacuumAtlas.Variation.RN.isTangent_b (M Q : ℝ) :
    IsTangent (fun ε => gRN M (Q ^ 2 + ε)) (fun _ => faradayRN Q) domJ tanB 0 := by sorry
