-- Prove2me | Theorems.Thm_ExactVacuumAtlas_Controls_Shear_pullback
-- name    : ExactVacuumAtlas.Controls.Shear.pullback
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-15T20:39:01.758485+00:00
-- url     : https://prove2.me/theorems/1eebfa19-3878-450a-8d68-258e4dc3f3cc
-- title:
--   Pull-back identity Jᵀ h(Φ x) J = gCtl λ (x)
-- statement:
--   For every real λ and x ∈ domEF: (jacShear λ x)ᵀ · gCyl 0 (shear λ x) · jacShear λ x = gCtl λ (x).
-- source:
--   He Wang, Exact Vacuum Atlas II, local source snapshot (public Git repository not yet available), commit 11fb317259353b71a41d6daed466c495cffd7db4; Atlas/Controls/Shear.lean#L103-L109; SHA-256 219b8cea95eaf75ce7002541a89f6bcd6bdaeacb3ba69ac402eaacd84c242ddc. Mathematical background: See mission/PHYSICS_BOUNDARY.md §A-F for registered definitions and literature references (Wald, Müller-Grave arXiv:0904.4184, Visser arXiv:0706.0622, Martel-Poisson gr-qc/0001069).

import Mathlib
import Definitions.Def_Atlas_Controls_CylinderTables
import Definitions.Def_Atlas_Controls_Shear
import Definitions.Def_Atlas_Controls_ShearTables
import Definitions.Def_Atlas_Core_Basic
import Definitions.Def_Atlas_Core_Certificate
import Definitions.Def_Atlas_Core_Lift
import Definitions.Def_Atlas_Core_Relation
import Definitions.Def_Atlas_Schwarzschild_Defs
import Definitions.Def_Atlas_Schwarzschild_Domain
import Definitions.Def_Atlas_Transport_Connection
import Definitions.Def_Atlas_Transport_Curvature
import Definitions.Def_Atlas_Transport_MatrixCalc
open Real
open scoped ContDiff
open Matrix
open ExactVacuumAtlas ExactVacuumAtlas.Schwarzschild
open ExactVacuumAtlas
open ExactVacuumAtlas.Controls
open ExactVacuumAtlas.Controls.Shear
set_option maxHeartbeats 4000000
variable (lam : ℝ)

theorem ExactVacuumAtlas.Controls.Shear.pullback {x : Pt 4} (hx : x ∈ domEF) :
    (jacShear lam x)ᵀ * metricMatrix (Cylinder.gCyl 0) (shear lam x) * jacShear lam x
      = metricMatrix (gCtl lam) x := by sorry
