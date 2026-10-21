-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_KN_domReg_nonempty
-- name    : ExactVacuumAtlas.EinsteinMaxwell.KN.domReg_nonempty
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-21T01:46:11.283098+00:00
-- url     : https://prove2.me/theorems/db94264b-ef55-4fbd-a38a-ac50ee9e8915
-- title:
--   domReg is nonempty
-- statement:
--   domReg is nonempty
--
--   domReg M a Q is nonempty for every real M, a, Q.
--
--   **Scope.** Exactly the hypotheses printed in the formal statement.
--
--   **中文摘要** domReg 非空。
-- source:
--   He Wang, Exact Spacetime Atlas IV: Certified Einstein–Maxwell Backgrounds and First Variations. Local source, no public repository; commit 543904bfcfa3bb169f43fc4d9dbd569999b71886; Atlas/EinsteinMaxwell/KN/Domain.lean#L113-L125; SHA-256 2cba50578710c01bc97b197588f366c9fd153ed1add83d7d7577383f23a9ccce. Registered definitions and literature: mission/PHYSICS_BOUNDARY.md (§H–§J); Müller–Grave arXiv:0904.4184; Newman et al., J. Math. Phys. 6 (1965) 918.

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

theorem ExactVacuumAtlas.EinsteinMaxwell.KN.domReg_nonempty (M a Q : ℝ) : (domReg M a Q).Nonempty := by sorry
