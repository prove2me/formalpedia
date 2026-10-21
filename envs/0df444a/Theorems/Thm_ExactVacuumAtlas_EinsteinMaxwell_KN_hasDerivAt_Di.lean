-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_KN_hasDerivAt_Di
-- name    : ExactVacuumAtlas.EinsteinMaxwell.KN.hasDerivAt_Di
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-21T01:44:27.647853+00:00
-- url     : https://prove2.me/theorems/cb7e6291-0003-4dde-97d5-f0304b0f8164
-- title:
--   Derivative of the atom 1/Δ
-- statement:
--   Derivative of the atom 1/Δ
--
--   HasDerivAt (u ↦ Di M a Q u) (−(2r − 2M) Di²) at r with Δ(r) ≠ 0.
--
--   **Scope.** Exactly the hypotheses printed in the formal statement.
--
--   **中文摘要** 原子 1/Δ 的导数。
-- source:
--   He Wang, Exact Spacetime Atlas IV: Certified Einstein–Maxwell Backgrounds and First Variations. Local source, no public repository; commit 543904bfcfa3bb169f43fc4d9dbd569999b71886; Atlas/EinsteinMaxwell/KN/Domain.lean#L27-L37; SHA-256 2cba50578710c01bc97b197588f366c9fd153ed1add83d7d7577383f23a9ccce. Registered definitions and literature: mission/PHYSICS_BOUNDARY.md (§H–§J); Müller–Grave arXiv:0904.4184; Newman et al., J. Math. Phys. 6 (1965) 918.

import Mathlib
import Definitions.Def_Atlas_Core_Basic
import Definitions.Def_Atlas_Core_Lift
import Definitions.Def_Atlas_EinsteinMaxwell_Basic
import Definitions.Def_Atlas_EinsteinMaxwell_KN_Defs
import Definitions.Def_Atlas_EinsteinMaxwell_KN_Domain
import Definitions.Def_Atlas_Kerr_InAtoms
open Real
open ExactVacuumAtlas
open ExactVacuumAtlas.EinsteinMaxwell
open ExactVacuumAtlas.EinsteinMaxwell.KN
open ExactVacuumAtlas.Kerr.In (Ui Wi)

theorem ExactVacuumAtlas.EinsteinMaxwell.KN.hasDerivAt_Di (M a Q r : ℝ) (h : r ^ 2 - 2 * M * r + a ^ 2 + Q ^ 2 ≠ 0) :
    HasDerivAt (fun u => Di M a Q u) (-(2 * r - 2 * M) * Di M a Q r ^ 2) r := by sorry
