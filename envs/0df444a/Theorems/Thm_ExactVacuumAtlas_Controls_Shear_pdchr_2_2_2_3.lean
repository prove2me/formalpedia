-- Prove2me | Theorems.Thm_ExactVacuumAtlas_Controls_Shear_pdchr_2_2_2_3
-- name    : ExactVacuumAtlas.Controls.Shear.pdchr_2_2_2_3
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-15T20:36:01.077995+00:00
-- url     : https://prove2.me/theorems/f304bb1c-0622-4963-b959-6cd615f6a5cf
-- title:
--   pdchr 2 2 2 3
-- statement:
--   For every real $\lambda$ and $x=(T,R,\alpha,\beta)$ with $R>0$ and $0<\alpha<\pi$, use the sheared control metric $g_{\mathrm{Ctl},\lambda}$ and its stated inverse. Then
--
--   $$\partial_{\alpha}\Gamma^{2}_{23} = -\lambda(\cos^3\alpha-2\cos\alpha\sin^2\alpha).$$
--
--   This is the derivative of the indicated Christoffel component, not a claim of zero curvature. The coordinate index 2 denotes alpha.
-- source:
--   He Wang, Exact Vacuum Atlas II, local source snapshot (public Git repository not yet available), commit 11fb317259353b71a41d6daed466c495cffd7db4; Atlas/Controls/ShearTables.lean#L1255-L1260; SHA-256 782cc8c1c151bbdb9e599ba53ea76ee6c2e4203bbca394d8de7a4b95ac66b98e. Mathematical background: See mission/PHYSICS_BOUNDARY.md §A-F for registered definitions and literature references (Wald, Müller-Grave arXiv:0904.4184, Visser arXiv:0706.0622, Martel-Poisson gr-qc/0001069).

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

theorem ExactVacuumAtlas.Controls.Shear.pdchr_2_2_2_3 (x : Pt 4) (hx : x ∈ domEF)  :
    pd 2 (christoffel (gCtl lam) (giCtl lam) 2 2 3) x = -(lam * (cos (x 2) ^ 3 - 2 * cos (x 2) * sin (x 2) ^ 2)) := by sorry
