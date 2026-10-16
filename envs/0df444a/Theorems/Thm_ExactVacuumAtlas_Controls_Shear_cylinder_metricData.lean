-- Prove2me | Theorems.Thm_ExactVacuumAtlas_Controls_Shear_cylinder_metricData
-- name    : ExactVacuumAtlas.Controls.Shear.cylinder_metricData
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-15T19:40:45.224257+00:00
-- url     : https://prove2.me/theorems/c65df21e-7189-42bc-9b6e-063af96f7dd6
-- title:
--   Metric data of the release-I cylinder control
-- statement:
--   MetricData (gCyl 0) (giCyl 0) domEF: domEF open, gCyl 0 = diag(−1, 1, 1, sin²θ) symmetric, giCyl 0 · gCyl 0 = I on domEF (sin θ ≠ 0 there), all components C^∞ on domEF. No curvature condition (this metric is not vacuum).
-- source:
--   He Wang, Exact Vacuum Atlas II, local source snapshot (public Git repository not yet available), commit 11fb317259353b71a41d6daed466c495cffd7db4; Atlas/Controls/Shear.lean#L145-L159; SHA-256 219b8cea95eaf75ce7002541a89f6bcd6bdaeacb3ba69ac402eaacd84c242ddc. Mathematical background: See mission/PHYSICS_BOUNDARY.md §A-F for registered definitions and literature references (Wald, Müller-Grave arXiv:0904.4184, Visser arXiv:0706.0622, Martel-Poisson gr-qc/0001069).

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

theorem ExactVacuumAtlas.Controls.Shear.cylinder_metricData : MetricData (Cylinder.gCyl 0) (Cylinder.giCyl 0) domEF := by sorry
