-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_EinsteinMaxwellCertificate_mono
-- name    : ExactVacuumAtlas.EinsteinMaxwell.EinsteinMaxwellCertificate.mono
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-21T01:44:03.504817+00:00
-- url     : https://prove2.me/theorems/c54181e4-8eca-4faf-8cb5-1f42d32d4836
-- title:
--   Certificate restriction to an open subset
-- statement:
--   Certificate restriction to an open subset
--
--   An Einstein–Maxwell certificate on U restricts to every open nonempty V ⊆ U.
--
--   **Scope.** Exactly the hypotheses printed in the formal statement.
--
--   **中文摘要** 证书限制到开子集。
-- source:
--   He Wang, Exact Spacetime Atlas IV: Certified Einstein–Maxwell Backgrounds and First Variations. Local source, no public repository; commit 543904bfcfa3bb169f43fc4d9dbd569999b71886; Atlas/EinsteinMaxwell/Transfer.lean#L33-L47; SHA-256 406c2eab6eaa154112760347f130ff5f2181e38eaa0539f514f2ab3e9a58c93c. Registered definitions and literature: mission/PHYSICS_BOUNDARY.md (§H–§J); Müller–Grave arXiv:0904.4184; Newman et al., J. Math. Phys. 6 (1965) 918.

import Mathlib
import Definitions.Def_Atlas_Core_Basic
import Definitions.Def_Atlas_Core_Certificate
import Definitions.Def_Atlas_EinsteinMaxwell_Basic
import Definitions.Def_Atlas_EinsteinMaxwell_Certificate
open scoped ContDiff
open ExactVacuumAtlas
open ExactVacuumAtlas.EinsteinMaxwell
variable {g ginv : Metric 4} {F : TwoForm 4} {U : Set (Pt 4)}

theorem ExactVacuumAtlas.EinsteinMaxwell.EinsteinMaxwellCertificate.mono (h : EinsteinMaxwellCertificate g ginv F U) {V : Set (Pt 4)} (hVU : V ⊆ U)
    (hV : IsOpen V) (hne : V.Nonempty) : EinsteinMaxwellCertificate g ginv F V := by sorry
