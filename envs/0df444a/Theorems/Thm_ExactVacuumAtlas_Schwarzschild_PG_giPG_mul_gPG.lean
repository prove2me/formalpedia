-- Prove2me | Theorems.Thm_ExactVacuumAtlas_Schwarzschild_PG_giPG_mul_gPG
-- name    : ExactVacuumAtlas.Schwarzschild.PG.giPG_mul_gPG
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-16T02:30:16.313374+00:00
-- url     : https://prove2.me/theorems/7778c18f-d987-453a-9631-b54b90ad5b35
-- title:
--   giPG is a genuine left inverse of gPG on domEF
-- statement:
--   For all real M ≥ 0, ε with ε² = 1, and x ∈ domEF: giPG M ε (x) · gPG M ε (x) = I (uses q² = 2M/r and ε² = 1 in the (T, r) block).
-- source:
--   He Wang, Exact Vacuum Atlas II, local source snapshot (public Git repository not yet available), commit 11fb317259353b71a41d6daed466c495cffd7db4; Atlas/Schwarzschild/PGTransport.lean#L28-L43; SHA-256 21d7802bc903aa00fee3b30ad8bd8c392d214d0c016091aad5299c0d904b982f. Mathematical background: See mission/PHYSICS_BOUNDARY.md §A-F for registered definitions and literature references (Wald, Müller-Grave arXiv:0904.4184, Visser arXiv:0706.0622, Martel-Poisson gr-qc/0001069).

import Mathlib
import Definitions.Def_Atlas_Core_Basic
import Definitions.Def_Atlas_Core_Certificate
import Definitions.Def_Atlas_Core_Lift
import Definitions.Def_Atlas_Core_Relation
import Definitions.Def_Atlas_Schwarzschild_Defs
import Definitions.Def_Atlas_Schwarzschild_Domain
import Definitions.Def_Atlas_Schwarzschild_PGDefs
import Definitions.Def_Atlas_Schwarzschild_PGRelation
import Definitions.Def_Atlas_Transport_Connection
import Definitions.Def_Atlas_Transport_Curvature
import Definitions.Def_Atlas_Transport_MatrixCalc
open Real
open ExactVacuumAtlas ExactVacuumAtlas.Schwarzschild
open ExactVacuumAtlas
open ExactVacuumAtlas.Schwarzschild
open ExactVacuumAtlas.Schwarzschild.PG
set_option maxHeartbeats 4000000
variable (M ε : ℝ)

theorem ExactVacuumAtlas.Schwarzschild.PG.giPG_mul_gPG (hM : 0 ≤ M) (hε : ε ^ 2 = 1) {x : Pt 4} (hx : x ∈ domEF) :
    metricMatrix (giPG M ε) x * metricMatrix (gPG M ε) x = 1 := by sorry
