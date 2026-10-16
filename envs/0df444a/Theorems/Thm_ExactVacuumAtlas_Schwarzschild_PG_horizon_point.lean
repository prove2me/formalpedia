-- Prove2me | Theorems.Thm_ExactVacuumAtlas_Schwarzschild_PG_horizon_point
-- name    : ExactVacuumAtlas.Schwarzschild.PG.horizon_point
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-16T02:29:37.010504+00:00
-- url     : https://prove2.me/theorems/97864257-c61c-4280-891b-32edeb5917ec
-- title:
--   For M > 0 the certified PG domain contains r = 2M with Ricci = 0 there
-- statement:
--   For all real M > 0 and ε with ε² = 1: there exists x ∈ domEF with x 1 = 2M such that Ric(gPG M ε, giPG M ε)_{bd}(x) = 0 for all b, d (witness: the equatorial point (0, 2M, π/2, 0)).
-- source:
--   He Wang, Exact Vacuum Atlas II, local source snapshot (public Git repository not yet available), commit 11fb317259353b71a41d6daed466c495cffd7db4; Atlas/Schwarzschild/PGSpecial.lean#L59-L64; SHA-256 2eb0a573868512cad1044bf8af89a5f34de57d1da1c39075e5f4e87eecd7defa. Mathematical background: See mission/PHYSICS_BOUNDARY.md §A-F for registered definitions and literature references (Wald, Müller-Grave arXiv:0904.4184, Visser arXiv:0706.0622, Martel-Poisson gr-qc/0001069).

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

theorem ExactVacuumAtlas.Schwarzschild.PG.horizon_point (M ε : ℝ) (hM : 0 < M) (hε : ε ^ 2 = 1) :
    ∃ x ∈ domEF, x 1 = 2 * M ∧ ∀ b d, ricciOf (gPG M ε) (giPG M ε) b d x = 0 := by sorry
