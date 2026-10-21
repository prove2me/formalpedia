-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_KN_inv_3_0
-- name    : ExactVacuumAtlas.EinsteinMaxwell.KN.inv_3_0
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-21T01:47:36.862836+00:00
-- url     : https://prove2.me/theorems/383a8d4e-e710-4e71-9166-90c51fb9073a
-- title:
--   KN inverse check, entry (3, 0)
-- statement:
--   KN inverse check, entry (3, 0)
--
--   Entry (3, 0) of giKN · gKN equals the identity entry where Σ, Δ, sin θ ≠ 0.
--
--   **Scope.** Exactly the hypotheses printed in the formal statement.
--
--   **中文摘要** KN 逆矩阵检验的一个分量。
-- source:
--   He Wang, Exact Spacetime Atlas IV: Certified Einstein–Maxwell Backgrounds and First Variations. Local source, no public repository; commit 543904bfcfa3bb169f43fc4d9dbd569999b71886; Atlas/EinsteinMaxwell/KN/Parts.lean#L192-L205; SHA-256 27df3365e1b568e37410fd5ea573366b73f33888fe24ccbe6f7bc357788ceccc. Registered definitions and literature: mission/PHYSICS_BOUNDARY.md (§H–§J); Müller–Grave arXiv:0904.4184; Newman et al., J. Math. Phys. 6 (1965) 918.

import Mathlib
import Definitions.Def_Atlas_Core_Basic
import Definitions.Def_Atlas_Core_Lift
import Definitions.Def_Atlas_EinsteinMaxwell_Basic
import Definitions.Def_Atlas_EinsteinMaxwell_KN_Defs
import Definitions.Def_Atlas_EinsteinMaxwell_KN_Domain
import Definitions.Def_Atlas_Kerr_Frame
import Definitions.Def_Atlas_Kerr_InAtoms
import Definitions.Def_KerrBL_CoordGeometry
import Definitions.Def_KerrBL_Kerr_Metric
open Real
open ExactVacuumAtlas
open scoped ContDiff
open ExactVacuumAtlas.Kerr.In (Ui Wi)
open ExactVacuumAtlas
open ExactVacuumAtlas.EinsteinMaxwell
open ExactVacuumAtlas.EinsteinMaxwell.KN
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
variable (M a Q : ℝ)

theorem ExactVacuumAtlas.EinsteinMaxwell.KN.inv_3_0 (x : Pt 4) (hS : x 1 ^ 2 + a ^ 2 * cos (x 2) ^ 2 ≠ 0) (hD : x 1 ^ 2 - 2 * M * x 1 + a ^ 2 + Q ^ 2 ≠ 0) (hs : sin (x 2) ≠ 0) :
    (metricMatrix (giKN M a Q) x * metricMatrix (gKN M a Q) x) 3 0 = 0 := by sorry
