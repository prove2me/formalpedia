-- Prove2me | Theorems.Thm_ExactVacuumAtlas_Controls_Cylinder_pdchr_2_2_3_3
-- name    : ExactVacuumAtlas.Controls.Cylinder.pdchr_2_2_3_3
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-15T19:02:55.13374+00:00
-- url     : https://prove2.me/theorems/56fc908d-e8b1-47f8-870e-21fecf5e958a
-- title:
--   pdchr 2 2 3 3
-- statement:
--   For every real $M$ (an unused parameter) and $x=(t,r,\theta,\varphi)$ with $r>0$ and $0<\theta<\pi$, the cylinder metric $g=\operatorname{diag}(-1,1,1,\sin^2\theta)$ and its stated inverse satisfy
--
--   $$\partial_{\theta}\Gamma^{2}_{33} = -(\cos^2\theta-\sin^2\theta).$$
--
--   This is the derivative of the indicated Christoffel component, not a claim of zero curvature. The coordinate index 2 denotes theta.
-- source:
--   He Wang, Exact Vacuum Atlas II, local source snapshot (public Git repository not yet available), commit 11fb317259353b71a41d6daed466c495cffd7db4; Atlas/Controls/CylinderTables.lean#L1230-L1235; SHA-256 6853c22124c397d8886c39820e0325b7348d66f0d0a916d41678b132205ebfee. Mathematical background: See mission/PHYSICS_BOUNDARY.md §A-F for registered definitions and literature references (Wald, Müller-Grave arXiv:0904.4184, Visser arXiv:0706.0622, Martel-Poisson gr-qc/0001069).

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

theorem ExactVacuumAtlas.Controls.Cylinder.pdchr_2_2_3_3 (x : Pt 4) (hx : x ∈ domEF)  :
    pd 2 (christoffel (gCyl M) (giCyl M) 2 3 3) x = (-1) * (cos (x 2) ^ 2 - sin (x 2) ^ 2) := by sorry
