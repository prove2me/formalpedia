-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_KN_certReg
-- name    : ExactVacuumAtlas.EinsteinMaxwell.KN.certReg
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-21T01:48:48.124912+00:00
-- url     : https://prove2.me/theorems/df011de7-05be-470d-a8b3-af934728526f
-- title:
--   KN certificate on the regular set
-- statement:
--   KN certificate on the regular set
--
--   For every real M, a, Q: EinsteinMaxwellCertificate (gKN) (giKN) (faradayKN) (domReg M a Q) (both signs of Δ).
--
--   **Scope.** Exactly the hypotheses printed in the formal statement.
--
--   **中文摘要** KN 在正则集 domReg 上的完整证书（任意实参数）。
-- source:
--   He Wang, Exact Spacetime Atlas IV: Certified Einstein–Maxwell Backgrounds and First Variations. Local source, no public repository; commit 543904bfcfa3bb169f43fc4d9dbd569999b71886; Atlas/EinsteinMaxwell/KN/Cert.lean#L210-L224; SHA-256 83d8b851ed8987c89596808d4357bed8ec1ac87efc28a406c3573f1bec168e4c. Registered definitions and literature: mission/PHYSICS_BOUNDARY.md (§H–§J); Müller–Grave arXiv:0904.4184; Newman et al., J. Math. Phys. 6 (1965) 918.

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

theorem ExactVacuumAtlas.EinsteinMaxwell.KN.certReg (M a Q : ℝ) :
    EinsteinMaxwellCertificate (gKN M a Q) (giKN M a Q) (faradayKN a Q) (domReg M a Q) := by sorry
