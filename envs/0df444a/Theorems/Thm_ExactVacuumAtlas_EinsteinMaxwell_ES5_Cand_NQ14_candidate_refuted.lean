-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_ES5_Cand_NQ14_candidate_refuted
-- name    : ExactVacuumAtlas.EinsteinMaxwell.ES5.Cand.NQ14.candidate_refuted
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-28T14:08:28.806797+00:00
-- url     : https://prove2.me/theorems/08a9a3fc-64cd-4b71-90e8-fe59d67bc9e7
-- title:
--   NQ14 (wrong charge): no Einstein–Maxwell certificate
-- statement:
--   NQ14 (wrong charge): no Einstein–Maxwell certificate
--
--   ¬ EMCertificateD candG candGi candF dom for the ST03 metric (β = 1/3) with the wrong potential Φ = −2/(2r²) (charge 2), dom = esDomain {r | 0 < r ∧ rX r ≠ 0}, rX r = r⁴ − 2r² + 1/3. Refutes the EINSTEIN–MAXWELL certificate.
--
--   **Scope.** Fixed rational parameters transcribed from the candidate JSON; domain dom = esDomain radR with radR = {r | 0 < r ∧ rX r ≠ 0}; no horizon/axis regularity.
--
--   **中文摘要** NQ14（错误电荷）：不存在 Einstein–Maxwell 证书（否定的是 EMCertificateD）。
-- source:
--   He Wang, Exact Spacetime Atlas VI: Five-Dimensional Einstein–Maxwell Certificates and Equal-Spin Radial Reduction. Local source, no public repository; commit 4a4048a; Atlas/EinsteinMaxwell/ES5/Cand/NQ14/Cert.lean#L18-L22; SHA-256 785a4615b3fad98d122d8a81ebae3a85efa777df0f9472c611487f7db55de306. Registered definitions: mission/PHYSICS_BOUNDARY.md (§N–§O); literature: R. C. Myers, M. J. Perry, Ann. Phys. 172 (1986) 304; F. R. Tangherlini, Nuovo Cimento 27 (1963) 636.

import Mathlib
import Definitions.Def_Atlas_Core_Basic
import Definitions.Def_Atlas_Core_Certificate
import Definitions.Def_Atlas_EinsteinMaxwell_Basic
import Definitions.Def_Atlas_EinsteinMaxwell_D_Basic
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_Cand_NQ14_Defs
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_Cand_NQ14_EM
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_Defs
open scoped ContDiff
open ExactVacuumAtlas ExactVacuumAtlas.EinsteinMaxwell ExactVacuumAtlas.EinsteinMaxwell.D
open ExactVacuumAtlas.EinsteinMaxwell.ES5
open ExactVacuumAtlas
open ExactVacuumAtlas.EinsteinMaxwell
open ExactVacuumAtlas.EinsteinMaxwell.ES5
open ExactVacuumAtlas.EinsteinMaxwell.ES5.Cand
open ExactVacuumAtlas.EinsteinMaxwell.ES5.Cand.NQ14
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

theorem ExactVacuumAtlas.EinsteinMaxwell.ES5.Cand.NQ14.candidate_refuted : ¬ EMCertificateD candG candGi candF dom := by sorry
