-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_KN_einstein
-- name    : ExactVacuumAtlas.EinsteinMaxwell.KN.einstein
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-21T01:47:33.469982+00:00
-- url     : https://prove2.me/theorems/b545232a-977a-41a6-8114-7131ce08f030
-- title:
--   KN Einstein residual vanishes
-- statement:
--   KN Einstein residual vanishes
--
--   einsteinMaxwell (gKN) (giKN) (faradayKN) i j = 0 on domReg M a Q, all i, j.
--
--   **Scope.** Exactly the hypotheses printed in the formal statement.
--
--   **中文摘要** KN 的 E = 0（domReg 上）。
-- source:
--   He Wang, Exact Spacetime Atlas IV: Certified Einstein–Maxwell Backgrounds and First Variations. Local source, no public repository; commit 543904bfcfa3bb169f43fc4d9dbd569999b71886; Atlas/EinsteinMaxwell/KN/Cert.lean#L200-L204; SHA-256 83d8b851ed8987c89596808d4357bed8ec1ac87efc28a406c3573f1bec168e4c. Registered definitions and literature: mission/PHYSICS_BOUNDARY.md (§H–§J); Müller–Grave arXiv:0904.4184; Newman et al., J. Math. Phys. 6 (1965) 918.

import Mathlib
import Definitions.Def_Atlas_Core_Basic
import Definitions.Def_Atlas_Core_Certificate
import Definitions.Def_Atlas_Core_Lift
import Definitions.Def_Atlas_EinsteinMaxwell_Basic
import Definitions.Def_Atlas_EinsteinMaxwell_Certificate
import Definitions.Def_Atlas_EinsteinMaxwell_KN_Defs
import Definitions.Def_Atlas_EinsteinMaxwell_KN_Domain
import Definitions.Def_Atlas_Kerr_Frame
import Definitions.Def_Atlas_Kerr_InAtoms
import Definitions.Def_KerrBL_CoordGeometry
import Definitions.Def_KerrBL_Kerr_Metric
open Real
open scoped ContDiff

theorem ExactVacuumAtlas.EinsteinMaxwell.KN.einstein (M a Q : ℝ) {x : Pt 4} (hx : x ∈ domReg M a Q) (i j : Fin 4) :
    einsteinMaxwell (gKN M a Q) (giKN M a Q) (faradayKN a Q) i j x = 0 := by sorry
