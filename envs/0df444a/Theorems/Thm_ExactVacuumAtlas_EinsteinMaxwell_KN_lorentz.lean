-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_KN_lorentz
-- name    : ExactVacuumAtlas.EinsteinMaxwell.KN.lorentz
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-21T01:49:08.146589+00:00
-- url     : https://prove2.me/theorems/cc211407-0781-491b-ab83-3ac725c7cb2c
-- title:
--   KN metric is Lorentzian
-- statement:
--   KN metric is Lorentzian
--
--   IsLorentzian (gKN M a Q) on domReg (Carter-type frames for Δ > 0 and Δ < 0).
--
--   **Scope.** Exactly the hypotheses printed in the formal statement.
--
--   **中文摘要** KN 度规 Lorentz 号差。
-- source:
--   He Wang, Exact Spacetime Atlas IV: Certified Einstein–Maxwell Backgrounds and First Variations. Local source, no public repository; commit 543904bfcfa3bb169f43fc4d9dbd569999b71886; Atlas/EinsteinMaxwell/KN/Cert.lean#L76-L110; SHA-256 83d8b851ed8987c89596808d4357bed8ec1ac87efc28a406c3573f1bec168e4c. Registered definitions and literature: mission/PHYSICS_BOUNDARY.md (§H–§J); Müller–Grave arXiv:0904.4184; Newman et al., J. Math. Phys. 6 (1965) 918.

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

theorem ExactVacuumAtlas.EinsteinMaxwell.KN.lorentz (M a Q : ℝ) {x : Pt 4} (hx : x ∈ domReg M a Q) :
    IsLorentzian (metricMatrix (gKN M a Q) x) := by sorry
