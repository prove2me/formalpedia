-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_ES5_Cand_NW01_candidate_refuted
-- name    : ExactVacuumAtlas.EinsteinMaxwell.ES5.Cand.NW01.candidate_refuted
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-28T14:08:38.180963+00:00
-- url     : https://prove2.me/theorems/5c3cf9a6-8cca-48ac-8ab0-3264ffa462b4
-- title:
--   NW01 (wrong rotation W): no Ricci-flat certificate
-- statement:
--   NW01 (wrong rotation W): no Ricci-flat certificate
--
--   ¬ VacuumCertificate candG candGi dom for the MP01 data with the wrong W = μa/(r²+a²)² (μ = 3, a = 1/2; the term μa² is missing from the denominator), dom = esDomain {r | 0 < r ∧ rX r ≠ 0}, rX r = (r² + (1/2)²)² − 3r². Refutes the VACUUM certificate.
--
--   **Scope.** Fixed rational parameters transcribed from the candidate JSON; domain dom = esDomain radR with radR = {r | 0 < r ∧ rX r ≠ 0}; no horizon/axis regularity.
--
--   **中文摘要** NW01（错误的 W）：不存在 Ricci 平坦证书（否定的是 VacuumCertificate）。
-- source:
--   He Wang, Exact Spacetime Atlas VI: Five-Dimensional Einstein–Maxwell Certificates and Equal-Spin Radial Reduction. Local source, no public repository; commit 4a4048a; Atlas/EinsteinMaxwell/ES5/Cand/NW01/Cert.lean#L18-L21; SHA-256 153facf7b53f94cdab80e60b994cc30b718f38d33d4f9285953032b39f749dec. Registered definitions: mission/PHYSICS_BOUNDARY.md (§N–§O); literature: R. C. Myers, M. J. Perry, Ann. Phys. 172 (1986) 304; F. R. Tangherlini, Nuovo Cimento 27 (1963) 636.

import Mathlib
import Definitions.Def_Atlas_Core_Basic
import Definitions.Def_Atlas_Core_Certificate
import Definitions.Def_Atlas_EinsteinMaxwell_Basic
import Definitions.Def_Atlas_EinsteinMaxwell_D_Basic
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_Cand_NW01_Defs
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_Defs
open scoped ContDiff
open ExactVacuumAtlas ExactVacuumAtlas.EinsteinMaxwell ExactVacuumAtlas.EinsteinMaxwell.D
open ExactVacuumAtlas.EinsteinMaxwell.ES5
open ExactVacuumAtlas
open ExactVacuumAtlas.EinsteinMaxwell
open ExactVacuumAtlas.EinsteinMaxwell.ES5
open ExactVacuumAtlas.EinsteinMaxwell.ES5.Cand
open ExactVacuumAtlas.EinsteinMaxwell.ES5.Cand.NW01
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

theorem ExactVacuumAtlas.EinsteinMaxwell.ES5.Cand.NW01.candidate_refuted : ¬ VacuumCertificate candG candGi dom := by sorry
