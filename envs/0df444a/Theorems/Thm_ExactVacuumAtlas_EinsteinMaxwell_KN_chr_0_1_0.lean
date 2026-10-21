-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_KN_chr_0_1_0
-- name    : ExactVacuumAtlas.EinsteinMaxwell.KN.chr_0_1_0
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-21T01:44:36.125989+00:00
-- url     : https://prove2.me/theorems/ccfd8af2-edd0-48a3-8beb-27a9c88bb184
-- title:
--   KN Christoffel symbol Γ^0_{10}
-- statement:
--   KN Christoffel symbol Γ^0_{10}
--
--   Closed form of christoffel (gKN) (giKN) 0 1 0 where Σ, Δ, sin θ ≠ 0.
--
--   **Scope.** Exactly the hypotheses printed in the formal statement.
--
--   **中文摘要** KN Christoffel 符号闭式。
-- source:
--   He Wang, Exact Spacetime Atlas IV: Certified Einstein–Maxwell Backgrounds and First Variations. Local source, no public repository; commit 543904bfcfa3bb169f43fc4d9dbd569999b71886; Atlas/EinsteinMaxwell/KN/Tables.lean#L422-L435; SHA-256 82a10a4f76cd734d52eeb263411fc37d6c5cd44401612f53bdcd45891d6d7739. Registered definitions and literature: mission/PHYSICS_BOUNDARY.md (§H–§J); Müller–Grave arXiv:0904.4184; Newman et al., J. Math. Phys. 6 (1965) 918.

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

theorem ExactVacuumAtlas.EinsteinMaxwell.KN.chr_0_1_0 (x : Pt 4) (hS : x 1 ^ 2 + a ^ 2 * cos (x 2) ^ 2 ≠ 0) (hD : x 1 ^ 2 - 2 * M * x 1 + a ^ 2 + Q ^ 2 ≠ 0) (hs : sin (x 2) ≠ 0) :
    christoffel (gKN M a Q) (giKN M a Q) 0 1 0 x = ((1:ℝ) * M * a^4) * sin (x 2) ^ 2 * Ui a (x 1) (x 2) ^ 2 * Di M a Q (x 1) + ((-1:ℝ) * M * a^4) * Ui a (x 1) (x 2) ^ 2 * Di M a Q (x 1) + ((1:ℝ) * M * a^2) * (x 1) ^ 2 * sin (x 2) ^ 2 * Ui a (x 1) (x 2) ^ 2 * Di M a Q (x 1) + ((1:ℝ) * M) * (x 1) ^ 4 * Ui a (x 1) (x 2) ^ 2 * Di M a Q (x 1) + ((-1:ℝ) * a^2 * Q^2) * (x 1) * Ui a (x 1) (x 2) ^ 2 * Di M a Q (x 1) + ((-1:ℝ) * Q^2) * (x 1) ^ 3 * Ui a (x 1) (x 2) ^ 2 * Di M a Q (x 1) := by sorry
