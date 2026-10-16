-- Prove2me | Theorems.Thm_ExactVacuumAtlas_Controls_Shear_mixed_witness
-- name    : ExactVacuumAtlas.Controls.Shear.mixed_witness
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-15T20:37:58.427192+00:00
-- url     : https://prove2.me/theorems/a213a712-c1d4-4c6c-9f65-5775399fd941
-- title:
--   R₂₃ = √2/4 at λ = 1 and the point (0, 1, π/4, 0)
-- statement:
--   Ric(gCtl 1, giCtl 1)_{23}(pt) = √2/4 with pt = (0, 1, π/4, 0).
-- source:
--   He Wang, Exact Vacuum Atlas II, local source snapshot (public Git repository not yet available), commit 11fb317259353b71a41d6daed466c495cffd7db4; Atlas/Controls/Shear.lean#L205-L212; SHA-256 219b8cea95eaf75ce7002541a89f6bcd6bdaeacb3ba69ac402eaacd84c242ddc. Mathematical background: See mission/PHYSICS_BOUNDARY.md §A-F for registered definitions and literature references (Wald, Müller-Grave arXiv:0904.4184, Visser arXiv:0706.0622, Martel-Poisson gr-qc/0001069).

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

theorem ExactVacuumAtlas.Controls.Shear.mixed_witness : ricciOf (gCtl 1) (giCtl 1) 2 3 pt = Real.sqrt 2 / 4 := by sorry
