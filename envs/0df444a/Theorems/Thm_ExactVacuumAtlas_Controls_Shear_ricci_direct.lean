-- Prove2me | Theorems.Thm_ExactVacuumAtlas_Controls_Shear_ricci_direct
-- name    : ExactVacuumAtlas.Controls.Shear.ricci_direct
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-15T20:37:27.447202+00:00
-- url     : https://prove2.me/theorems/27983736-8342-43d7-a056-f935dd3aa876
-- title:
--   Sixteen Ricci components of the sheared cylinder metric from generated tables
-- statement:
--   For every real λ, x ∈ domEF and b, d: Ric(gCtl λ, giCtl λ)_{bd}(x) = ctlR λ b d x (the statement wrapped by control_direct).
-- source:
--   He Wang, Exact Vacuum Atlas II, local source snapshot (public Git repository not yet available), commit 11fb317259353b71a41d6daed466c495cffd7db4; Atlas/Controls/Shear.lean#L169-L176; SHA-256 219b8cea95eaf75ce7002541a89f6bcd6bdaeacb3ba69ac402eaacd84c242ddc. Mathematical background: See mission/PHYSICS_BOUNDARY.md §A-F for registered definitions and literature references (Wald, Müller-Grave arXiv:0904.4184, Visser arXiv:0706.0622, Martel-Poisson gr-qc/0001069).

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

theorem ExactVacuumAtlas.Controls.Shear.ricci_direct {x : Pt 4} (hx : x ∈ domEF) (b d : Fin 4) :
    ricciOf (gCtl lam) (giCtl lam) b d x = ctlR lam b d x := by sorry
