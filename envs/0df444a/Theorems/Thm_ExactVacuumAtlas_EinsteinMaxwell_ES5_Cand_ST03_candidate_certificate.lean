-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_ES5_Cand_ST03_candidate_certificate
-- name    : ExactVacuumAtlas.EinsteinMaxwell.ES5.Cand.ST03.candidate_certificate
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-28T14:16:31.428423+00:00
-- url     : https://prove2.me/theorems/9e068a1a-e71a-414f-9808-65d0563c7a1d
-- title:
--   ST03 (μ = 2, Q = 1, β = 1/3): static charged Einstein–Maxwell certificate
-- statement:
--   ST03 (μ = 2, Q = 1, β = 1/3): static charged Einstein–Maxwell certificate
--
--   EMCertificateD candG candGi candF dom for B = (r⁴ − 2r² + 1/3)/r⁴ = 1 − 2/r² + (1/3)/r⁴, D = 1/B (as transcribed: r⁴/(r⁴ − 2r² + 1/3)), A = H = r², W = 0, Φ = −1/(2r²), Ψ = 0, candF = esFaraday rPhi rPsi = d(Φ dt), dom = esDomain {r | 0 < r ∧ rX r ≠ 0}, rX r = r⁴ − 2r² + 1/3. One fixed static charged instance (3β = Q² holds: 3·(1/3) = 1²).
--
--   **Scope.** Fixed rational parameters transcribed from the candidate JSON; domain dom = esDomain radR with radR = {r | 0 < r ∧ rX r ≠ 0}; no horizon/axis regularity.
--
--   **中文摘要** ST03（μ=2, Q=1, β=1/3）静态带电固定实例的 Einstein–Maxwell 证书。
-- source:
--   He Wang, Exact Spacetime Atlas VI: Five-Dimensional Einstein–Maxwell Certificates and Equal-Spin Radial Reduction. Local source, no public repository; commit 4a4048a; Atlas/EinsteinMaxwell/ES5/Cand/ST03/Cert.lean#L36-L51; SHA-256 564f74cf05b6c7e73bbcbc3af7a380b2732bd50c7f512d2b726a794d3e2ce870. Registered definitions: mission/PHYSICS_BOUNDARY.md (§N–§O); literature: R. C. Myers, M. J. Perry, Ann. Phys. 172 (1986) 304; F. R. Tangherlini, Nuovo Cimento 27 (1963) 636.

import Mathlib
import Definitions.Def_Atlas_Core_Basic
import Definitions.Def_Atlas_Core_Certificate
import Definitions.Def_Atlas_EinsteinMaxwell_Basic
import Definitions.Def_Atlas_EinsteinMaxwell_D_Basic
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_Cand_ST03_Defs
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_Cand_ST03_EM
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_Defs
open scoped ContDiff
open ExactVacuumAtlas ExactVacuumAtlas.EinsteinMaxwell ExactVacuumAtlas.EinsteinMaxwell.D
open ExactVacuumAtlas.EinsteinMaxwell.ES5
open ExactVacuumAtlas
open ExactVacuumAtlas.EinsteinMaxwell
open ExactVacuumAtlas.EinsteinMaxwell.ES5
open ExactVacuumAtlas.EinsteinMaxwell.ES5.Cand
open ExactVacuumAtlas.EinsteinMaxwell.ES5.Cand.ST03
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

theorem ExactVacuumAtlas.EinsteinMaxwell.ES5.Cand.ST03.candidate_certificate : EMCertificateD candG candGi candF dom := by sorry
