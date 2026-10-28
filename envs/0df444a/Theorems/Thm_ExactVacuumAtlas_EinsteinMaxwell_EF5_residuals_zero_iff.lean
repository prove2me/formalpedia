-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_EF5_residuals_zero_iff
-- name    : ExactVacuumAtlas.EinsteinMaxwell.EF5.residuals_zero_iff
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-28T13:47:33.258462+00:00
-- url     : https://prove2.me/theorems/b9e394b6-81ad-46f7-b227-16a8307c1b57
-- title:
--   EF5 residual form: E = J = H = 0 on domU5 iff 3β = Q²
-- statement:
--   EF5 residual form: E = J = H = 0 on domU5 iff 3β = Q²
--
--   For all real μ, β, Q: (∀ x ∈ domU5, (∀ a b, einsteinMaxwellD (gEF5 μ β) (giEF5 μ β) (faraday5 Q) a b x = 0) ∧ (∀ j, maxwellDiv … j x = 0) ∧ (∀ i j k, faradayCyclic (faraday5 Q) i j k x = 0)) ⇔ 3β = Q².
--
--   **Scope.** All real μ, β, Q (no sign, horizon or sub-extremality restriction); domain domU5 = {x | 0 < x 1 ∧ 0 < x 2 ∧ x 2 < 1} (r > 0, 0 < u < 1; the zeros of f are NOT excised).
--
--   **中文摘要** 对所有实数 μ, β, Q：domU5 上 Einstein–Maxwell、Maxwell、Bianchi 残差全为零 ⇔ 3β = Q²。
-- source:
--   He Wang, Exact Spacetime Atlas VI: Five-Dimensional Einstein–Maxwell Certificates and Equal-Spin Radial Reduction. Local source, no public repository; commit 4a4048a; Atlas/EinsteinMaxwell/EF5/CertificateEF5.lean#L63-L75; SHA-256 cfead95b85a714aef90d980c00d0cf62ef54959a25cf5716e7e611261a95d8d3. Registered definitions: mission/PHYSICS_BOUNDARY.md (§N–§O); literature: R. C. Myers, M. J. Perry, Ann. Phys. 172 (1986) 304; F. R. Tangherlini, Nuovo Cimento 27 (1963) 636.

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

theorem ExactVacuumAtlas.EinsteinMaxwell.EF5.residuals_zero_iff (mu beta Q : ℝ) :
    (∀ x ∈ domU5,
      (∀ a b, einsteinMaxwellD (gEF5 mu beta) (giEF5 mu beta) (faraday5 Q) a b x = 0) ∧
      (∀ j, maxwellDiv (gEF5 mu beta) (giEF5 mu beta) (faraday5 Q) j x = 0) ∧
      (∀ i j k, faradayCyclic (faraday5 Q) i j k x = 0)) ↔ 3 * beta = Q ^ 2 := by sorry
