-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_ES5_Generic_field_equations_iff
-- name    : ExactVacuumAtlas.EinsteinMaxwell.ES5.Generic.field_equations_iff
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-28T14:06:33.693997+00:00
-- url     : https://prove2.me/theorems/c6f67bda-5d12-415b-8dc3-777021ad4ecc
-- title:
--   Pointwise completeness of the seven reduced radial equations
-- statement:
--   Pointwise completeness of the seven reduced radial equations
--
--   Under ESData R B D A H W Φ Ψ, for every x ∈ esDomain R: (all 25 components einsteinMaxwellD … a b x = 0 ∧ all 5 maxwellDiv … b x = 0 ∧ all 125 faradayCyclic (esFaraday Φ Ψ) a b c x = 0) ⇔ (redE_tt = redE_tσ = redE_rr = redE_uu = redE_σσ = 0 ∧ redJ_t = redJ_σ = 0 at r = x 1). The Bianchi (closedness) part holds identically because F = d𝒜.
--
--   **Scope.** All radial data (B, D, A, H, W, Φ, Ψ : ℝ → ℝ) and every R : Set ℝ with ESData R B D A H W Φ Ψ (R open, the seven functions C^∞ on R, B, D, A, H ≠ 0 on R); domain esDomain R = {x | x 1 ∈ R ∧ 0 < x 2 ∧ x 2 < 1}.
--
--   **中文摘要** 在 ESData 下，esDomain R 的每一点：25 个 Einstein–Maxwell、5 个 Maxwell、125 个 Bianchi 分量全为零 ⇔ r = x 1 处七个约化方程为零（Bianchi 部分恒成立）。
-- source:
--   He Wang, Exact Spacetime Atlas VI: Five-Dimensional Einstein–Maxwell Certificates and Equal-Spin Radial Reduction. Local source, no public repository; commit 4a4048a; Atlas/EinsteinMaxwell/ES5/Generic/Cert.lean#L34-L50; SHA-256 00f3159ba0b7e5c087d91eec1041c5509c00076fc91c64bcdcf812e38816579e. Registered definitions: mission/PHYSICS_BOUNDARY.md (§N–§O); literature: R. C. Myers, M. J. Perry, Ann. Phys. 172 (1986) 304; F. R. Tangherlini, Nuovo Cimento 27 (1963) 636.

import Mathlib
import Definitions.Def_Atlas_Core_Basic
import Definitions.Def_Atlas_Core_Certificate
import Definitions.Def_Atlas_EinsteinMaxwell_Basic
import Definitions.Def_Atlas_EinsteinMaxwell_D_Basic
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_Defs
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_Generic_Cert
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_Generic_Data
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_Generic_Reduced
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_Generic_Tables
open scoped ContDiff
open ExactVacuumAtlas ExactVacuumAtlas.EinsteinMaxwell ExactVacuumAtlas.EinsteinMaxwell.D
open ExactVacuumAtlas.EinsteinMaxwell.ES5
open ExactVacuumAtlas
open ExactVacuumAtlas.EinsteinMaxwell
open ExactVacuumAtlas.EinsteinMaxwell.ES5
open ExactVacuumAtlas.EinsteinMaxwell.ES5.Generic
variable {R : Set ℝ} {B D A H W Φ Ψ : ℝ → ℝ}

theorem ExactVacuumAtlas.EinsteinMaxwell.ES5.Generic.field_equations_iff (hE : ESData R B D A H W Φ Ψ) (x : Pt 5) (hx : x ∈ esDomain R) :
    ((∀ a b, einsteinMaxwellD (esMetric B D A H W) (esInverse B D A H W) (esFaraday Φ Ψ) a b x = 0) ∧
      (∀ b, maxwellDiv (esMetric B D A H W) (esInverse B D A H W) (esFaraday Φ Ψ) b x = 0) ∧
      (∀ a b c, faradayCyclic (esFaraday Φ Ψ) a b c x = 0)) ↔
    (redE_tt B D A H W Φ Ψ (x 1) = 0 ∧ redE_tσ B D A H W Φ Ψ (x 1) = 0 ∧
      redE_rr B D A H W Φ Ψ (x 1) = 0 ∧ redE_uu B D A H W Φ Ψ (x 1) = 0 ∧
      redE_σσ B D A H W Φ Ψ (x 1) = 0 ∧ redJ_t B D A H W Φ Ψ (x 1) = 0 ∧
      redJ_σ B D A H W Φ Ψ (x 1) = 0) := by sorry
