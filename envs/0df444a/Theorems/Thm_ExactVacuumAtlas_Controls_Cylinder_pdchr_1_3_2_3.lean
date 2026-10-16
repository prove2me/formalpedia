-- Prove2me | Theorems.Thm_ExactVacuumAtlas_Controls_Cylinder_pdchr_1_3_2_3
-- name    : ExactVacuumAtlas.Controls.Cylinder.pdchr_1_3_2_3
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-15T19:00:53.27066+00:00
-- url     : https://prove2.me/theorems/c5d04cf2-ed00-4df0-a3f6-93b2eec972f6
-- title:
--   pdchr 1 3 2 3
-- statement:
--   Partial derivative d_{1} Gamma^3_{23} of the cylinder metric: for every real M (unused) and (t,r,theta,phi) in domEF, d_{1} Gamma^3_{23}(gCyl M, giCyl M)(x) = 0. Intermediate entry for the cylinder Ricci table.
-- source:
--   He Wang, Exact Vacuum Atlas II, local source snapshot (public Git repository not yet available), commit 11fb317259353b71a41d6daed466c495cffd7db4; Atlas/Controls/CylinderTables.lean#L1068-L1073; SHA-256 6853c22124c397d8886c39820e0325b7348d66f0d0a916d41678b132205ebfee. Mathematical background: See mission/PHYSICS_BOUNDARY.md §A-F for registered definitions and literature references (Wald, Müller-Grave arXiv:0904.4184, Visser arXiv:0706.0622, Martel-Poisson gr-qc/0001069).

import Mathlib
import Definitions.Def_Atlas_Controls_CylinderTables
import Definitions.Def_Atlas_Core_Basic
import Definitions.Def_Atlas_Core_Lift
import Definitions.Def_Atlas_Schwarzschild_Defs
import Definitions.Def_Atlas_Schwarzschild_Domain
open Real
open ExactVacuumAtlas ExactVacuumAtlas.Schwarzschild
open ExactVacuumAtlas
open ExactVacuumAtlas.Controls
open ExactVacuumAtlas.Controls.Cylinder
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
variable (M : ℝ)

theorem ExactVacuumAtlas.Controls.Cylinder.pdchr_1_3_2_3 (x : Pt 4) (hx : x ∈ domEF)  :
    pd 1 (christoffel (gCyl M) (giCyl M) 3 2 3) x = 0 := by sorry
