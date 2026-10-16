-- Prove2me | Theorems.Thm_ExactVacuumAtlas_Controls_Shear_pdchr_1_3_3_3
-- name    : ExactVacuumAtlas.Controls.Shear.pdchr_1_3_3_3
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-15T19:48:59.199014+00:00
-- url     : https://prove2.me/theorems/ab815bb9-1dfa-4bfb-abd4-b46ece606a6e
-- title:
--   pdchr 1 3 3 3
-- statement:
--   Partial derivative d_{1} Gamma^3_{33} of the sheared control metric: for every real lam and (T,R,alpha,beta) in domEF, d_{1} Gamma^3_{33}(gCtl lam, giCtl lam)(x) = 0. Intermediate closed-form entry used in the Ricci computation for Shear.ricci_direct.
-- source:
--   He Wang, Exact Vacuum Atlas II, local source snapshot (public Git repository not yet available), commit 11fb317259353b71a41d6daed466c495cffd7db4; Atlas/Controls/ShearTables.lean#L1117-L1122; SHA-256 782cc8c1c151bbdb9e599ba53ea76ee6c2e4203bbca394d8de7a4b95ac66b98e. Mathematical background: See mission/PHYSICS_BOUNDARY.md §A-F for registered definitions and literature references (Wald, Müller-Grave arXiv:0904.4184, Visser arXiv:0706.0622, Martel-Poisson gr-qc/0001069).

import Mathlib
import Definitions.Def_Atlas_Controls_ShearTables
import Definitions.Def_Atlas_Core_Basic
import Definitions.Def_Atlas_Core_Lift
import Definitions.Def_Atlas_Schwarzschild_Defs
import Definitions.Def_Atlas_Schwarzschild_Domain
open Real
open ExactVacuumAtlas ExactVacuumAtlas.Schwarzschild
open ExactVacuumAtlas
open ExactVacuumAtlas.Controls
open ExactVacuumAtlas.Controls.Shear
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
variable (lam : ℝ)

theorem ExactVacuumAtlas.Controls.Shear.pdchr_1_3_3_3 (x : Pt 4) (hx : x ∈ domEF)  :
    pd 1 (christoffel (gCtl lam) (giCtl lam) 3 3 3) x = 0 := by sorry
