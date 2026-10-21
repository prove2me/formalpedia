-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_KN_isOpen_domReg
-- name    : ExactVacuumAtlas.EinsteinMaxwell.KN.isOpen_domReg
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-21T01:46:44.117678+00:00
-- url     : https://prove2.me/theorems/8bec0e68-739e-4b0a-b9aa-e771317c7464
-- title:
--   domReg is open
-- statement:
--   domReg is open
--
--   domReg M a Q = {Σ ≠ 0, Δ ≠ 0, sin θ ≠ 0} is open for every real M, a, Q.
--
--   **Scope.** Exactly the hypotheses printed in the formal statement.
--
--   **中文摘要** domReg 为开集。
-- source:
--   He Wang, Exact Spacetime Atlas IV: Certified Einstein–Maxwell Backgrounds and First Variations. Local source, no public repository; commit 543904bfcfa3bb169f43fc4d9dbd569999b71886; Atlas/EinsteinMaxwell/KN/Domain.lean#L52-L61; SHA-256 2cba50578710c01bc97b197588f366c9fd153ed1add83d7d7577383f23a9ccce. Registered definitions and literature: mission/PHYSICS_BOUNDARY.md (§H–§J); Müller–Grave arXiv:0904.4184; Newman et al., J. Math. Phys. 6 (1965) 918.

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

theorem ExactVacuumAtlas.EinsteinMaxwell.KN.isOpen_domReg (M a Q : ℝ) : IsOpen (domReg M a Q) := by sorry
