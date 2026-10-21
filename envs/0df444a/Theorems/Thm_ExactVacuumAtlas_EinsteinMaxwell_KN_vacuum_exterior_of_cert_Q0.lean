-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_KN_vacuum_exterior_of_cert_Q0
-- name    : ExactVacuumAtlas.EinsteinMaxwell.KN.vacuum_exterior_of_cert_Q0
-- status  : Open
-- author  : @He Wang
-- created : 2026-10-21T01:49:07.62054+00:00
-- url     : https://prove2.me/theorems/54e79218-8ca2-4e5a-9c7d-2281ee07d842
-- title:
--   KN at Q = 0 gives the Kerr BL vacuum certificate on the exterior
-- statement:
--   KN at Q = 0 gives the Kerr BL vacuum certificate on the exterior
--
--   For M > 0 and real a: VacuumCertificate (KerrBL.gKerr M a) (KerrBL.giKerr M a) (domKN M a 0), where gKerr, giKerr are the published TASK-001A Kerr Boyer–Lindquist definitions and VacuumCertificate is the release-I definition (open, nonempty, symmetric, true inverse, C^∞, Lorentzian, ricciOf = 0). Obtained from the KN certificate at Q = 0 (F = 0) by componentwise equality of the data on the common domain.
--
--   **Scope.** Parameter substitution Q = 0 on a common open domain; nothing for Q ≠ 0 is inferred from Kerr; independent of Verified.Kerr.
--
--   **中文摘要** Q = 0 特化：由 KN 证书导出 Kerr BL 真空证书（外域，M>0）；参数代入，不是极限。
-- source:
--   He Wang, Exact Spacetime Atlas IV: Certified Einstein–Maxwell Backgrounds and First Variations. Local source, no public repository; commit 543904bfcfa3bb169f43fc4d9dbd569999b71886; Atlas/EinsteinMaxwell/KN/Special.lean#L1618-L1623; SHA-256 8ec8234538cef3eac7f462a57128cdaa80597af52a2efef1190c8df8425ba5a3. Registered definitions and literature: mission/PHYSICS_BOUNDARY.md (§H–§J); Müller–Grave arXiv:0904.4184; Newman et al., J. Math. Phys. 6 (1965) 918.

import Mathlib
import Definitions.Def_Atlas_Core_Basic
import Definitions.Def_Atlas_Core_Certificate
import Definitions.Def_Atlas_Core_Lift
import Definitions.Def_Atlas_EinsteinMaxwell_Basic
import Definitions.Def_Atlas_EinsteinMaxwell_Certificate
import Definitions.Def_Atlas_EinsteinMaxwell_KN_Defs
import Definitions.Def_Atlas_EinsteinMaxwell_KN_Domain
import Definitions.Def_Atlas_EinsteinMaxwell_RNStd_Defs
import Definitions.Def_Atlas_Kerr_Frame
import Definitions.Def_Atlas_Kerr_InAtoms
import Definitions.Def_KerrBL_CoordGeometry
import Definitions.Def_KerrBL_Kerr_Metric
open Real
open scoped ContDiff
open ExactVacuumAtlas
open ExactVacuumAtlas.EinsteinMaxwell
open ExactVacuumAtlas.EinsteinMaxwell.KN
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

theorem ExactVacuumAtlas.EinsteinMaxwell.KN.vacuum_exterior_of_cert_Q0 (M a : ℝ) (hM : 0 < M) :
    VacuumCertificate (KerrBL.gKerr M a) (KerrBL.giKerr M a) (domKN M a 0) := by sorry
