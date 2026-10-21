-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_RN_isOpen_domRN
-- name    : ExactVacuumAtlas.EinsteinMaxwell.RN.isOpen_domRN
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-21T01:48:41.689676+00:00
-- url     : https://prove2.me/theorems/5f98a52a-7411-43a0-8d2b-50a63a86d6c3
-- title:
--   domRN is open
-- statement:
--   domRN is open
--
--   domRN = {r > 0, 0 < θ < π} is open.
--
--   **Scope.** Exactly the hypotheses printed in the formal statement.
--
--   **中文摘要** domRN 为开集。
-- source:
--   He Wang, Exact Spacetime Atlas IV: Certified Einstein–Maxwell Backgrounds and First Variations. Local source, no public repository; commit 543904bfcfa3bb169f43fc4d9dbd569999b71886; Atlas/EinsteinMaxwell/RN/Defs.lean#L84-L88; SHA-256 cadc562b90c2275f662a6587efb55e4c8d258c908477e2ca90b1ba3458587d99. Registered definitions and literature: mission/PHYSICS_BOUNDARY.md (§H–§J); Müller–Grave arXiv:0904.4184; Newman et al., J. Math. Phys. 6 (1965) 918.

import Mathlib
import Definitions.Def_Atlas_Core_Basic
import Definitions.Def_Atlas_EinsteinMaxwell_Basic
import Definitions.Def_Atlas_EinsteinMaxwell_RN_Defs
open Real

theorem ExactVacuumAtlas.EinsteinMaxwell.RN.isOpen_domRN : IsOpen domRN := by sorry
