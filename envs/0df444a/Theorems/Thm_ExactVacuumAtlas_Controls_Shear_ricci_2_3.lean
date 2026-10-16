-- Prove2me | Theorems.Thm_ExactVacuumAtlas_Controls_Shear_ricci_2_3
-- name    : ExactVacuumAtlas.Controls.Shear.ricci_2_3
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-15T20:36:35.065976+00:00
-- url     : https://prove2.me/theorems/8266cf71-4acf-4252-a017-733b0001f0df
-- title:
--   ricci 2 3
-- statement:
--   For every real $\lambda$ and $x=(T,R,\alpha,\beta)$ with $R>0$ and $0<\alpha<\pi$, the coordinate Ricci tensor of $g_{\mathrm{Ctl},\lambda}$ with its stated inverse satisfies
--
--   $$R_{23} = \lambda\cos\alpha\sin^2\alpha.$$
--
--   The symmetric component $R_{32}$ has the same expression. This mixed component vanishes when $\lambda=0$ or $\cos\alpha=0$; it is not claimed nonzero for every parameter and point.
-- source:
--   He Wang, Exact Vacuum Atlas II, local source snapshot (public Git repository not yet available), commit 11fb317259353b71a41d6daed466c495cffd7db4; Atlas/Controls/ShearTables.lean#L1606-L1611; SHA-256 782cc8c1c151bbdb9e599ba53ea76ee6c2e4203bbca394d8de7a4b95ac66b98e. Mathematical background: See mission/PHYSICS_BOUNDARY.md §A-F for registered definitions and literature references (Wald, Müller-Grave arXiv:0904.4184, Visser arXiv:0706.0622, Martel-Poisson gr-qc/0001069).

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

theorem ExactVacuumAtlas.Controls.Shear.ricci_2_3 (x : Pt 4) (hx : x ∈ domEF)   :
    ricciOf (gCtl lam) (giCtl lam) 2 3 x = lam * (cos (x 2) * sin (x 2) ^ 2) := by sorry
