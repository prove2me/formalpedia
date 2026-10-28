-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_ES5_Generic_es_certificate_iff
-- name    : ExactVacuumAtlas.EinsteinMaxwell.ES5.Generic.es_certificate_iff
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-28T14:06:27.589485+00:00
-- url     : https://prove2.me/theorems/a968d63e-47f6-4d82-8233-c75fdd0b6318
-- title:
--   Atlas VI Goal: Einstein–Maxwell certificate of the equal-spin ansatz ⇔ seven reduced radial equations
-- statement:
--   Atlas VI Goal: Einstein–Maxwell certificate of the equal-spin ansatz ⇔ seven reduced radial equations
--
--   For radial data B, D, A, H, W, Φ, Ψ : ℝ → ℝ and R : Set ℝ with ESData R B D A H W Φ Ψ (R open; the seven functions C^∞ on R; B, D, A, H ≠ 0 on R), if R is nonempty and 0 < A r, 0 < H r, 0 < B r · D r for every r ∈ R, then EMCertificateD (esMetric B D A H W) (esInverse B D A H W) (esFaraday Φ Ψ) (esDomain R) holds if and only if ReducedSystem B D A H W Φ Ψ R, i.e. the five Einstein equations redE_tt, redE_tσ, redE_rr, redE_uu, redE_σσ and the two Maxwell equations redJ_t, redJ_σ vanish at every r ∈ R. Here esMetric = −B dt² + D dr² + A[du²/(4u(1−u)) + u(1−u)(dφ−dψ)²] + H(σ − W dt)², σ = u dφ + (1−u) dψ, esInverse is its explicit frame-form inverse, esFaraday Φ Ψ = d(Φ dt + Ψ σ), and esDomain R = {x | x 1 ∈ R ∧ 0 < x 2 < 1}. Both directions are proved.
--
--   **Scope.** All radial data (B, D, A, H, W, Φ, Ψ : ℝ → ℝ) and every R : Set ℝ with ESData R B D A H W Φ Ψ (R open, the seven functions C^∞ on R, B, D, A, H ≠ 0 on R); domain esDomain R = {x | x 1 ∈ R ∧ 0 < x 2 ∧ x 2 < 1}. The Goal adds exactly R.Nonempty and ∀ r ∈ R, 0 < A r ∧ 0 < H r ∧ 0 < B r * D r.
--
--   **中文摘要** 等自旋五维拟设：在 ESData（R 开、七个径向函数在 R 上 C^∞、B,D,A,H 非零）且 R 非空、A>0、H>0、BD>0 的前提下，esDomain R 上的 Einstein–Maxwell 证书 EMCertificateD 成立当且仅当 R 上五个 Einstein 与两个 Maxwell 约化径向方程全部为零。不假设 B>0、D>0、连通性或仅外域。
-- source:
--   He Wang, Exact Spacetime Atlas VI: Five-Dimensional Einstein–Maxwell Certificates and Equal-Spin Radial Reduction. Local source, no public repository; commit 4a4048a; Atlas/EinsteinMaxwell/ES5/Generic/Cert.lean#L52-L80; SHA-256 00f3159ba0b7e5c087d91eec1041c5509c00076fc91c64bcdcf812e38816579e. Registered definitions: mission/PHYSICS_BOUNDARY.md (§N–§O); literature: R. C. Myers, M. J. Perry, Ann. Phys. 172 (1986) 304; F. R. Tangherlini, Nuovo Cimento 27 (1963) 636.

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

theorem ExactVacuumAtlas.EinsteinMaxwell.ES5.Generic.es_certificate_iff (hE : ESData R B D A H W Φ Ψ) (hne : R.Nonempty)
    (hsig : ∀ r ∈ R, 0 < A r ∧ 0 < H r ∧ 0 < B r * D r) :
    EMCertificateD (esMetric B D A H W) (esInverse B D A H W) (esFaraday Φ Ψ) (esDomain R) ↔
      ReducedSystem B D A H W Φ Ψ R := by sorry
