-- Prove2me | Theorems.Thm_ExactVacuumAtlas_Variation_RN_familyData_b
-- name    : ExactVacuumAtlas.Variation.RN.familyData_b
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-21T01:50:54.709501+00:00
-- url     : https://prove2.me/theorems/e5ca1d3f-a8b1-46b1-a46c-e499d76cbd9f
-- title:
--   RN b-family is FamilyData
-- statement:
--   RN b-family is FamilyData
--
--   ε ↦ (gRN M (Q² + ε), giRN M (Q² + ε), faradayRN Q) satisfies FamilyData on domJ = ℝ × domRN.
--
--   **Scope.** Exactly the hypotheses printed in the formal statement.
--
--   **中文摘要** RN 的 b 族满足 FamilyData。
-- source:
--   He Wang, Exact Spacetime Atlas IV: Certified Einstein–Maxwell Backgrounds and First Variations. Local source, no public repository; commit 543904bfcfa3bb169f43fc4d9dbd569999b71886; Atlas/EinsteinMaxwell/Variation/RN.lean#L68-L83; SHA-256 7513cd6c91a5e550bb62e1cac2f2c8a8c17fa469087ba3c27bf9c1eab933f66f. Registered definitions and literature: mission/PHYSICS_BOUNDARY.md (§H–§J); Müller–Grave arXiv:0904.4184; Newman et al., J. Math. Phys. 6 (1965) 918.

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

theorem ExactVacuumAtlas.Variation.RN.familyData_b (M Q : ℝ) :
    FamilyData (fun ε => gRN M (Q ^ 2 + ε)) (fun ε => giRN M (Q ^ 2 + ε)) (fun _ => faradayRN Q) domJ := by sorry
