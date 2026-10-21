-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_KN_gi_3_0
-- name    : ExactVacuumAtlas.EinsteinMaxwell.KN.gi_3_0
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-21T01:44:38.531922+00:00
-- url     : https://prove2.me/theorems/e48d6c0d-8f86-4d9a-bce8-a8f778d7f459
-- title:
--   KN inverse component g^{30} in rational atoms
-- statement:
--   KN inverse component g^{30} in rational atoms
--
--   giKN M a Q at index (3, 0) in the atoms 1/Σ, 1/Δ.
--
--   **Scope.** Exactly the hypotheses printed in the formal statement.
--
--   **中文摘要** KN 逆度规分量闭式。
-- source:
--   He Wang, Exact Spacetime Atlas IV: Certified Einstein–Maxwell Backgrounds and First Variations. Local source, no public repository; commit 543904bfcfa3bb169f43fc4d9dbd569999b71886; Atlas/EinsteinMaxwell/KN/Tables.lean#L144-L148; SHA-256 82a10a4f76cd734d52eeb263411fc37d6c5cd44401612f53bdcd45891d6d7739. Registered definitions and literature: mission/PHYSICS_BOUNDARY.md (§H–§J); Müller–Grave arXiv:0904.4184; Newman et al., J. Math. Phys. 6 (1965) 918.

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

theorem ExactVacuumAtlas.EinsteinMaxwell.KN.gi_3_0 (x : Pt 4) : giKN M a Q 3 0 x = ((-2:ℝ) * M * a) * (x 1) * Ui a (x 1) (x 2) * Di M a Q (x 1) + ((1:ℝ) * a * Q^2) * Ui a (x 1) (x 2) * Di M a Q (x 1) := by sorry
