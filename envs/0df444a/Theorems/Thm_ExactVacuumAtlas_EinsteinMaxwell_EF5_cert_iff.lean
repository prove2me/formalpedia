-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_EF5_cert_iff
-- name    : ExactVacuumAtlas.EinsteinMaxwell.EF5.cert_iff
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-28T13:47:43.741908+00:00
-- url     : https://prove2.me/theorems/6851c1bd-c1a2-4f7c-af88-330d7a9a125c
-- title:
--   Five-dimensional EF Einstein–Maxwell matching: certificate iff 3β = Q²
-- statement:
--   Five-dimensional EF Einstein–Maxwell matching: certificate iff 3β = Q²
--
--   For all real μ, β, Q: EMCertificateD (gEF5 μ β) (giEF5 μ β) (faraday5 Q) domU5 ⇔ 3β = Q². Here gEF5 μ β = −f dv² + 2 dv dr + r²[du²/(4u(1−u)) + u dφ² + (1−u) dψ²] with f = 1 − μ/r² + β/r⁴, giEF5 its explicit inverse, faraday5 Q the field of A = −Q/(2r²) dv (F_10 = Q/r³ = −F_01), and domU5 = {0 < r, 0 < u < 1}. This is a criterion inside one fixed explicit static ansatz, not a classification of five-dimensional black holes; the normalisation 3β = Q² is derived, not assumed.
--
--   **Scope.** All real μ, β, Q (no sign, horizon or sub-extremality restriction); domain domU5 = {x | 0 < x 1 ∧ 0 < x 2 ∧ x 2 < 1} (r > 0, 0 < u < 1; the zeros of f are NOT excised).
--
--   **中文摘要** 对所有实数 μ, β, Q：固定的五维静态 EF 拟设在 domU5 上满足 Einstein–Maxwell 证书 ⇔ 3β = Q²。这是该拟设内的判据，不是五维黑洞的分类。
-- source:
--   He Wang, Exact Spacetime Atlas VI: Five-Dimensional Einstein–Maxwell Certificates and Equal-Spin Radial Reduction. Local source, no public repository; commit 4a4048a; Atlas/EinsteinMaxwell/EF5/CertificateEF5.lean#L77-L84; SHA-256 cfead95b85a714aef90d980c00d0cf62ef54959a25cf5716e7e611261a95d8d3. Registered definitions: mission/PHYSICS_BOUNDARY.md (§N–§O); literature: R. C. Myers, M. J. Perry, Ann. Phys. 172 (1986) 304; F. R. Tangherlini, Nuovo Cimento 27 (1963) 636.

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

theorem ExactVacuumAtlas.EinsteinMaxwell.EF5.cert_iff (mu beta Q : ℝ) :
    EMCertificateD (gEF5 mu beta) (giEF5 mu beta) (faraday5 Q) domU5 ↔ 3 * beta = Q ^ 2 := by sorry
