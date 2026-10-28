-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_D_EMCertificateD_congr_iff
-- name    : ExactVacuumAtlas.EinsteinMaxwell.D.EMCertificateD.congr_iff
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-28T13:40:40.882979+00:00
-- url     : https://prove2.me/theorems/a8dffa74-c8f2-4180-b904-bdee1e707f70
-- title:
--   Certificates depend only on the data on the domain
-- statement:
--   Certificates depend only on the data on the domain
--
--   In total dimension n + 1, for g ginv g' ginv' : Metric (n+1), F F' : TwoForm (n+1) and U: if g, ginv, F agree componentwise with g', ginv', F' on U (Set.EqOn), then EMCertificateD g ginv F U ⇔ EMCertificateD g' ginv' F' U.
--
--   **Scope.** Exactly the hypotheses printed in the formal statement.
--
--   **中文摘要** 总维数 n+1：若度规、逆度规与场强在 U 上逐分量相等，则两者的 EMCertificateD 等价。
-- source:
--   He Wang, Exact Spacetime Atlas VI: Five-Dimensional Einstein–Maxwell Certificates and Equal-Spin Radial Reduction. Local source, no public repository; commit 4a4048a; Atlas/EinsteinMaxwell/D/Transfer.lean#L70-L76; SHA-256 78a5207d09bd50bfc82e646cb5b085123303f7fabe24854bf0e65d16f2d7d9ae. Registered definitions: mission/PHYSICS_BOUNDARY.md (§N–§O); literature: R. C. Myers, M. J. Perry, Ann. Phys. 172 (1986) 304; F. R. Tangherlini, Nuovo Cimento 27 (1963) 636.

import Mathlib
import Definitions.Def_Atlas_Core_Basic
import Definitions.Def_Atlas_Core_Certificate
import Definitions.Def_Atlas_EinsteinMaxwell_Basic
import Definitions.Def_Atlas_EinsteinMaxwell_D_Basic
open scoped ContDiff
open ExactVacuumAtlas ExactVacuumAtlas.EinsteinMaxwell
open ExactVacuumAtlas
open ExactVacuumAtlas.EinsteinMaxwell
open ExactVacuumAtlas.EinsteinMaxwell.D
variable {n : ℕ} {g ginv : Metric (n + 1)} {F : TwoForm (n + 1)} {U : Set (Pt (n + 1))}

theorem ExactVacuumAtlas.EinsteinMaxwell.D.EMCertificateD.congr_iff {g' ginv' : Metric (n + 1)} {F' : TwoForm (n + 1)}
    (hg : ∀ i j, Set.EqOn (g i j) (g' i j) U) (hgi : ∀ i j, Set.EqOn (ginv i j) (ginv' i j) U)
    (hF : ∀ i j, Set.EqOn (F i j) (F' i j) U) :
    EMCertificateD g ginv F U ↔ EMCertificateD g' ginv' F' U := by sorry
