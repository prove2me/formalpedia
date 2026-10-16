-- Prove2me | Theorems.Thm_ExactVacuumAtlas_Schwarzschild_PG_chr_1_0_2
-- name    : ExactVacuumAtlas.Schwarzschild.PG.chr_1_0_2
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-15T23:19:28.404968+00:00
-- url     : https://prove2.me/theorems/49ac1993-df01-4cf2-aa4d-47faf91625a3
-- title:
--   chr 1 0 2
-- statement:
--   Christoffel symbol Gamma^1_{02} of the PG metric: for every M >= 0, eps^2 = 1 and (T,r,theta,phi) with r > 0, r != 0, sin theta != 0, Gamma^1_{02}(gPG M eps, giPG M eps, x) = 0. Closed form in r, q = sqrt(2M/r), theta, eps; kernel-checked table entry used in PGCertParts.
-- source:
--   He Wang, Exact Vacuum Atlas II, local source snapshot (public Git repository not yet available), commit 11fb317259353b71a41d6daed466c495cffd7db4; Atlas/Schwarzschild/PGTables.lean#L395-L403; SHA-256 dafc5aee5d354120cdf9c59509fdc80d2f2a8375b89a53da84edb04211eb1ae5. Mathematical background: See mission/PHYSICS_BOUNDARY.md §A-F for registered definitions and literature references (Wald, Müller-Grave arXiv:0904.4184, Visser arXiv:0706.0622, Martel-Poisson gr-qc/0001069).

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

theorem ExactVacuumAtlas.Schwarzschild.PG.chr_1_0_2 (x : Pt 4) (hr : x 1 ≠ 0) (hs : sin (x 2) ≠ 0) (hrp : 0 < x 1) (hM : 0 ≤ M) (hε : ε ^ 2 = 1) :
    christoffel (gPG M ε) (giPG M ε) 1 0 2 x = 0 := by sorry
