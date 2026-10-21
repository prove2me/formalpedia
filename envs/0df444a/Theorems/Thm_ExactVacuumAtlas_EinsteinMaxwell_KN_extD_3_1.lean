-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_KN_extD_3_1
-- name    : ExactVacuumAtlas.EinsteinMaxwell.KN.extD_3_1
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-21T01:46:02.456596+00:00
-- url     : https://prove2.me/theorems/11a14015-9806-4ae4-b149-7ef0391ae92d
-- title:
--   KN potential: (dA)_{31}
-- statement:
--   KN potential: (dA)_{31}
--
--   Closed form of extD (emPotentialKN a Q) at (3, 1) where Σ, Δ, sin θ ≠ 0.
--
--   **Scope.** Exactly the hypotheses printed in the formal statement.
--
--   **中文摘要** KN 势的外微分分量。
-- source:
--   He Wang, Exact Spacetime Atlas IV: Certified Einstein–Maxwell Backgrounds and First Variations. Local source, no public repository; commit 543904bfcfa3bb169f43fc4d9dbd569999b71886; Atlas/EinsteinMaxwell/KN/Fields.lean#L241-L254; SHA-256 1703a0db2829e50b9c78470ea77810c26f1971c65857e810049e5f3924cca0bd. Registered definitions and literature: mission/PHYSICS_BOUNDARY.md (§H–§J); Müller–Grave arXiv:0904.4184; Newman et al., J. Math. Phys. 6 (1965) 918.

import Mathlib
import Definitions.Def_Atlas_Core_Basic
import Definitions.Def_Atlas_Core_Lift
import Definitions.Def_Atlas_EinsteinMaxwell_Basic
import Definitions.Def_Atlas_EinsteinMaxwell_KN_Defs
import Definitions.Def_Atlas_EinsteinMaxwell_KN_Domain
import Definitions.Def_Atlas_Kerr_InAtoms
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

theorem ExactVacuumAtlas.EinsteinMaxwell.KN.extD_3_1 (x : Pt 4) (hS : x 1 ^ 2 + a ^ 2 * cos (x 2) ^ 2 ≠ 0) (hD : x 1 ^ 2 - 2 * M * x 1 + a ^ 2 + Q ^ 2 ≠ 0) (hs : sin (x 2) ≠ 0) :
    extD (emPotentialKN a Q) 3 1 x = ((-1:ℝ) * a^3 * Q) * sin (x 2) ^ 2 * cos (x 2) ^ 2 * Ui a (x 1) (x 2) ^ 2 + ((1:ℝ) * a * Q) * (x 1) ^ 2 * sin (x 2) ^ 2 * Ui a (x 1) (x 2) ^ 2 := by sorry
