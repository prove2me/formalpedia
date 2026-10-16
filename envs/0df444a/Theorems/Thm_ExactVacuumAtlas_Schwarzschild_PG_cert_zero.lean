-- Prove2me | Theorems.Thm_ExactVacuumAtlas_Schwarzschild_PG_cert_zero
-- name    : ExactVacuumAtlas.Schwarzschild.PG.cert_zero
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-15T22:33:59.059435+00:00
-- url     : https://prove2.me/theorems/007cce3d-9a06-42d3-84c1-9c6db6b9cbc4
-- title:
--   M = 0: PG data is Minkowski spherical data
-- statement:
--   For every real ε: VacuumCertificate (gPG 0 ε) (giPG 0 ε) domEF. At M = 0, q = √0 = 0, so gPG 0 ε = diag(−1, 1, r², r² sin²θ) = gSph on domEF (= domSph) for every ε; no condition ε² = 1 is needed.
-- source:
--   He Wang, Exact Vacuum Atlas II, local source snapshot (public Git repository not yet available), commit 11fb317259353b71a41d6daed466c495cffd7db4; Atlas/Schwarzschild/PGSpecial.lean#L40-L44; SHA-256 2eb0a573868512cad1044bf8af89a5f34de57d1da1c39075e5f4e87eecd7defa. Mathematical background: See mission/PHYSICS_BOUNDARY.md §A-F for registered definitions and literature references (Wald, Müller-Grave arXiv:0904.4184, Visser arXiv:0706.0622, Martel-Poisson gr-qc/0001069).

import Mathlib
import Definitions.Def_Atlas_Core_Basic
import Definitions.Def_Atlas_Core_Certificate
import Definitions.Def_Atlas_Core_Lift
import Definitions.Def_Atlas_Core_Relation
import Definitions.Def_Atlas_Minkowski_Spherical
import Definitions.Def_Atlas_Schwarzschild_Defs
import Definitions.Def_Atlas_Schwarzschild_Domain
import Definitions.Def_Atlas_Schwarzschild_PGCertParts
import Definitions.Def_Atlas_Schwarzschild_PGDefs
import Definitions.Def_Atlas_Schwarzschild_PGRelation
open Real
open scoped ContDiff
open ExactVacuumAtlas ExactVacuumAtlas.Schwarzschild
open ExactVacuumAtlas
open ExactVacuumAtlas.Schwarzschild
open ExactVacuumAtlas.Schwarzschild.PG
set_option maxHeartbeats 4000000

theorem ExactVacuumAtlas.Schwarzschild.PG.cert_zero (ε : ℝ) : VacuumCertificate (gPG 0 ε) (giPG 0 ε) domEF := by sorry
