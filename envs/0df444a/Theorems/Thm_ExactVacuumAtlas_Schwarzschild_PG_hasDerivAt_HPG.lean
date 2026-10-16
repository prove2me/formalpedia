-- Prove2me | Theorems.Thm_ExactVacuumAtlas_Schwarzschild_PG_hasDerivAt_HPG
-- name    : ExactVacuumAtlas.Schwarzschild.PG.hasDerivAt_HPG
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-15T22:35:53.493638+00:00
-- url     : https://prove2.me/theorems/a6cd32eb-80bb-4eba-8ea5-cb1d8912a8b2
-- title:
--   Derivative of the primitive H_M
-- statement:
--   For real M ≥ 0 and r > 0: u ↦ H_M(u) = u − 2√(2M)√u + 4M log(√u + √(2M)) has derivative 1/(1 + q(M, r)) at r (genuine derivative; r = 2M included).
-- source:
--   He Wang, Exact Vacuum Atlas II, local source snapshot (public Git repository not yet available), commit 11fb317259353b71a41d6daed466c495cffd7db4; Atlas/Schwarzschild/PGRelation.lean#L67-L95; SHA-256 15a42669f14c3556d812be0667228c735019b13b898fa9b0552c54b35498feb7. Mathematical background: See mission/PHYSICS_BOUNDARY.md §A-F for registered definitions and literature references (Wald, Müller-Grave arXiv:0904.4184, Visser arXiv:0706.0622, Martel-Poisson gr-qc/0001069).

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

theorem ExactVacuumAtlas.Schwarzschild.PG.hasDerivAt_HPG {M r : ℝ} (hM : 0 ≤ M) (hr : 0 < r) :
    HasDerivAt (fun u => HPG M u) (1 / (1 + qf M r)) r := by sorry
