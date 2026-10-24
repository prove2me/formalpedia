-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_KN_minv_0_3
-- name    : ExactVacuumAtlas.EinsteinMaxwell.KN.minv_0_3
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-23T10:18:52.235169+00:00
-- url     : https://prove2.me/theorems/3bf08934-ad42-46ad-8292-b545e74bf964
-- title:
--   KN inverse check, entry (0, 3)
-- statement:
--   KN inverse check, entry (0, 3)
--
--   Entry (0, 3) of gKN · giKN equals the identity entry where Σ, Δ, sin θ ≠ 0 (IV source lemma, inlined in IV, a separate node here).
--
--   **Scope.** Exactly the hypotheses printed in the formal statement.
--
--   **中文摘要** KN 逆矩阵检验分量（IV 源引理）。
-- source:
--   He Wang, Exact Spacetime Atlas V: From Linearized Einstein–Maxwell Equations to Kerr–Newman Radiation Systems. Local source, no public repository; commit b8cd107a558e153ed41fb4972ac5315499d14778; Atlas/EinsteinMaxwell/KN/Parts.lean#L74-L87; SHA-256 27df3365e1b568e37410fd5ea573366b73f33888fe24ccbe6f7bc357788ceccc. Registered definitions: mission/PHYSICS_BOUNDARY.md (§K–§M); literature: P. Hintz, arXiv:2609.33661 (v1); Mark–Yang–Zimmerman–Chen, arXiv:1409.5800 (v1).

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

theorem ExactVacuumAtlas.EinsteinMaxwell.KN.minv_0_3 (x : Pt 4) (hS : x 1 ^ 2 + a ^ 2 * cos (x 2) ^ 2 ≠ 0) (hD : x 1 ^ 2 - 2 * M * x 1 + a ^ 2 + Q ^ 2 ≠ 0) (hs : sin (x 2) ≠ 0) :
    (metricMatrix (gKN M a Q) x * metricMatrix (giKN M a Q) x) 0 3 = 0 := by sorry
