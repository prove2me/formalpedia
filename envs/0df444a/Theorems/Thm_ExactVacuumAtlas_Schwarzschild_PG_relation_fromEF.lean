-- Prove2me | Theorems.Thm_ExactVacuumAtlas_Schwarzschild_PG_relation_fromEF
-- name    : ExactVacuumAtlas.Schwarzschild.PG.relation_fromEF
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-16T02:29:42.945193+00:00
-- url     : https://prove2.me/theorems/34ffc293-8911-4480-8644-87ee9525cf08
-- title:
--   EF → PG coordinate relation on all of domEF
-- statement:
--   For all real M ≥ 0 and ε with ε² = 1: CoordRelation (gEF M ε) (gPG M ε) domEF domEF (pgFromEF M ε) (pgToEF M ε) (jacInv M ε) — the inverse direction with Jacobian jacInv (radial mixed entry −ε/(1+q)).
-- source:
--   He Wang, Exact Vacuum Atlas II, local source snapshot (public Git repository not yet available), commit 11fb317259353b71a41d6daed466c495cffd7db4; Atlas/Schwarzschild/PGRelation.lean#L242-L251; SHA-256 15a42669f14c3556d812be0667228c735019b13b898fa9b0552c54b35498feb7. Mathematical background: See mission/PHYSICS_BOUNDARY.md §A-F for registered definitions and literature references (Wald, Müller-Grave arXiv:0904.4184, Visser arXiv:0706.0622, Martel-Poisson gr-qc/0001069).

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

theorem ExactVacuumAtlas.Schwarzschild.PG.relation_fromEF (hM : 0 ≤ M) (hε : ε ^ 2 = 1) :
    CoordRelation (gEF M ε) (gPG M ε) domEF domEF (pgFromEF M ε) (pgToEF M ε) (jacInv M ε) := by sorry
