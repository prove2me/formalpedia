-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_EF5_vacuumCertificate_iff
-- name    : ExactVacuumAtlas.EinsteinMaxwell.EF5.vacuumCertificate_iff
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-28T13:47:54.545935+00:00
-- url     : https://prove2.me/theorems/e44edff7-4bf9-4959-8907-1c657db83d21
-- title:
--   Vacuum condition within the EF family: Ricci-flat certificate iff β = 0
-- statement:
--   Vacuum condition within the EF family: Ricci-flat certificate iff β = 0
--
--   For all real μ, β: VacuumCertificate (gEF5 μ β) (giEF5 μ β) domU5 ⇔ β = 0, where VacuumCertificate (Atlas I) asks for an open nonempty domain, symmetric C^∞ metric with C^∞ inverse, Lorentz signature and ricciOf = 0.
--
--   **Scope.** All real μ, β (no field strength appears); domain domU5 = {x | 0 < x 1 ∧ 0 < x 2 ∧ x 2 < 1}.
--
--   **中文摘要** 对所有实数 μ, β：EF 拟设在 domU5 上 Ricci 平坦证书 VacuumCertificate ⇔ β = 0。
-- source:
--   He Wang, Exact Spacetime Atlas VI: Five-Dimensional Einstein–Maxwell Certificates and Equal-Spin Radial Reduction. Local source, no public repository; commit 4a4048a; Atlas/EinsteinMaxwell/EF5/CertificateEF5.lean#L123-L145; SHA-256 cfead95b85a714aef90d980c00d0cf62ef54959a25cf5716e7e611261a95d8d3. Registered definitions: mission/PHYSICS_BOUNDARY.md (§N–§O); literature: R. C. Myers, M. J. Perry, Ann. Phys. 172 (1986) 304; F. R. Tangherlini, Nuovo Cimento 27 (1963) 636.

import Mathlib
import Definitions.Def_Atlas_Core_Basic
import Definitions.Def_Atlas_Core_Certificate
import Definitions.Def_Atlas_EinsteinMaxwell_Basic
import Definitions.Def_Atlas_EinsteinMaxwell_D_Basic
import Definitions.Def_Atlas_EinsteinMaxwell_EF5_CertificateEF5
import Definitions.Def_Atlas_EinsteinMaxwell_EF5_Defs
import Definitions.Def_Atlas_EinsteinMaxwell_EF5_EinsteinMaxwellEF5
import Definitions.Def_Atlas_EinsteinMaxwell_EF5_Frame
import Definitions.Def_Atlas_EinsteinMaxwell_EF5_RicciOffDiag
open scoped ContDiff
open ExactVacuumAtlas ExactVacuumAtlas.EinsteinMaxwell ExactVacuumAtlas.EinsteinMaxwell.D
open ExactVacuumAtlas.EinsteinMaxwell.EF5
open ExactVacuumAtlas
open ExactVacuumAtlas.EinsteinMaxwell
open ExactVacuumAtlas.EinsteinMaxwell.EF5
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

theorem ExactVacuumAtlas.EinsteinMaxwell.EF5.vacuumCertificate_iff (mu beta : ℝ) :
    VacuumCertificate (gEF5 mu beta) (giEF5 mu beta) domU5 ↔ beta = 0 := by sorry
