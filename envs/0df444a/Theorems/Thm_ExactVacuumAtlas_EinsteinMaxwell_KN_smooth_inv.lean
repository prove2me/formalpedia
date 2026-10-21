-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_KN_smooth_inv
-- name    : ExactVacuumAtlas.EinsteinMaxwell.KN.smooth_inv
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-21T01:49:00.108089+00:00
-- url     : https://prove2.me/theorems/6e1b4f52-08af-43b9-926e-9dd66e062cdb
-- title:
--   KN inverse is C^∞
-- statement:
--   KN inverse is C^∞
--
--   Each component of giKN M a Q is C^∞ on domReg.
--
--   **Scope.** Exactly the hypotheses printed in the formal statement.
--
--   **中文摘要** KN 逆度规 C^∞。
-- source:
--   He Wang, Exact Spacetime Atlas IV: Certified Einstein–Maxwell Backgrounds and First Variations. Local source, no public repository; commit 543904bfcfa3bb169f43fc4d9dbd569999b71886; Atlas/EinsteinMaxwell/KN/Cert.lean#L131-L148; SHA-256 83d8b851ed8987c89596808d4357bed8ec1ac87efc28a406c3573f1bec168e4c. Registered definitions and literature: mission/PHYSICS_BOUNDARY.md (§H–§J); Müller–Grave arXiv:0904.4184; Newman et al., J. Math. Phys. 6 (1965) 918.

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

theorem ExactVacuumAtlas.EinsteinMaxwell.KN.smooth_inv (M a Q : ℝ) (i j : Fin 4) : ContDiffOn ℝ ∞ (giKN M a Q i j) (domReg M a Q) := by sorry
