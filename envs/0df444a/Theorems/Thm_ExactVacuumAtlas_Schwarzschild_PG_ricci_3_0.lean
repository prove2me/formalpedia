-- Prove2me | Theorems.Thm_ExactVacuumAtlas_Schwarzschild_PG_ricci_3_0
-- name    : ExactVacuumAtlas.Schwarzschild.PG.ricci_3_0
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-16T02:28:55.662089+00:00
-- url     : https://prove2.me/theorems/de6c57cd-87ae-4a4e-82fe-551ec7c2a5fe
-- title:
--   ricci 3 0
-- statement:
--   Ricci component R_{30} of the PG metric (Ric = 0 on domEF): for every M >= 0, eps^2 = 1 and (T,r,theta,phi) in domEF = {r > 0, 0 < theta < pi}, Ric(gPG M eps, giPG M eps)_{30} = 0. All 16 PG Ricci components vanish; this table entry is one of the 16 assembled in PG.cert (route 1).
-- source:
--   He Wang, Exact Vacuum Atlas II, local source snapshot (public Git repository not yet available), commit 11fb317259353b71a41d6daed466c495cffd7db4; Atlas/Schwarzschild/PGTables.lean#L2056-L2066; SHA-256 dafc5aee5d354120cdf9c59509fdc80d2f2a8375b89a53da84edb04211eb1ae5. Mathematical background: See mission/PHYSICS_BOUNDARY.md §A-F for registered definitions and literature references (Wald, Müller-Grave arXiv:0904.4184, Visser arXiv:0706.0622, Martel-Poisson gr-qc/0001069).

import Mathlib
import Definitions.Def_Atlas_Core_Basic
import Definitions.Def_Atlas_Core_Lift
import Definitions.Def_Atlas_Schwarzschild_Defs
import Definitions.Def_Atlas_Schwarzschild_Domain
import Definitions.Def_Atlas_Schwarzschild_PGDefs
open Real
open ExactVacuumAtlas ExactVacuumAtlas.Schwarzschild
open ExactVacuumAtlas
open ExactVacuumAtlas.Schwarzschild
open ExactVacuumAtlas.Schwarzschild.PG
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
variable (M ε : ℝ)

theorem ExactVacuumAtlas.Schwarzschild.PG.ricci_3_0 (x : Pt 4) (hx : x ∈ domEF) (hM : 0 ≤ M) (hε : ε ^ 2 = 1) :
    ricciOf (gPG M ε) (giPG M ε) 3 0 x = 0 := by sorry
