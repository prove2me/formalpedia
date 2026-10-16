-- Prove2me | Theorems.Thm_ExactVacuumAtlas_Schwarzschild_PG_relation_toEF
-- name    : ExactVacuumAtlas.Schwarzschild.PG.relation_toEF
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-16T02:30:09.260516+00:00
-- url     : https://prove2.me/theorems/219ae8c0-f09c-44e3-85d0-8a4b4e7861b2
-- title:
--   PG → EF coordinate relation on all of domEF
-- statement:
--   For all real M ≥ 0 and ε with ε² = 1: CoordRelation (gPG M ε) (gEF M ε) domEF domEF (pgToEF M ε) (pgFromEF M ε) (jac M ε): pgToEF(T,r,θ,φ) = (T + ε H_M(r), r, θ, φ) and pgFromEF are mutually inverse, pgToEF maps domEF bijectively onto domEF, both are C^∞ on domEF, jac (radial mixed entry ε/(1+q), det 1) is the genuine Jacobian, and jacᵀ gEF(pgToEF x) jac = gPG x on domEF.
-- source:
--   He Wang, Exact Vacuum Atlas II, local source snapshot (public Git repository not yet available), commit 11fb317259353b71a41d6daed466c495cffd7db4; Atlas/Schwarzschild/PGRelation.lean#L229-L240; SHA-256 15a42669f14c3556d812be0667228c735019b13b898fa9b0552c54b35498feb7. Mathematical background: See mission/PHYSICS_BOUNDARY.md §A-F for registered definitions and literature references (Wald, Müller-Grave arXiv:0904.4184, Visser arXiv:0706.0622, Martel-Poisson gr-qc/0001069).

import Mathlib
import Definitions.Def_Atlas_Core_Basic
import Definitions.Def_Atlas_Core_Lift
import Definitions.Def_Atlas_Core_Relation
import Definitions.Def_Atlas_Schwarzschild_Defs
import Definitions.Def_Atlas_Schwarzschild_Domain
import Definitions.Def_Atlas_Schwarzschild_PGDefs
import Definitions.Def_Atlas_Schwarzschild_PGRelation
open Real
open scoped ContDiff
open ExactVacuumAtlas ExactVacuumAtlas.Schwarzschild
open ExactVacuumAtlas
open ExactVacuumAtlas.Schwarzschild
open ExactVacuumAtlas.Schwarzschild.PG
set_option maxHeartbeats 4000000
variable (M ε : ℝ)

theorem ExactVacuumAtlas.Schwarzschild.PG.relation_toEF (hM : 0 ≤ M) (hε : ε ^ 2 = 1) :
    CoordRelation (gPG M ε) (gEF M ε) domEF domEF (pgToEF M ε) (pgFromEF M ε) (jac M ε) := by sorry
