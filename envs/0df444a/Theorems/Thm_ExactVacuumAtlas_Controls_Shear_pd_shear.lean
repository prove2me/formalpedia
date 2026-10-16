-- Prove2me | Theorems.Thm_ExactVacuumAtlas_Controls_Shear_pd_shear
-- name    : ExactVacuumAtlas.Controls.Shear.pd_shear
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-15T19:35:10.594239+00:00
-- url     : https://prove2.me/theorems/5120d5b4-923e-4440-a0e5-9922bca165cd
-- title:
--   Genuine Jacobian of the shear map
-- statement:
--   For every real λ, every point x ∈ ℝ⁴ and all k, i: pd i (y ↦ shear λ y k) x = jacShear λ x k i, i.e. the slice derivatives of the components of Φ(T,R,α,β) = (T,R,α,β + λ sin α) are the entries of I + λ cos α E₃₂.
-- source:
--   He Wang, Exact Vacuum Atlas II, local source snapshot (public Git repository not yet available), commit 11fb317259353b71a41d6daed466c495cffd7db4; Atlas/Controls/Shear.lean#L87-L96; SHA-256 219b8cea95eaf75ce7002541a89f6bcd6bdaeacb3ba69ac402eaacd84c242ddc. Mathematical background: See mission/PHYSICS_BOUNDARY.md §A-F for registered definitions and literature references (Wald, Müller-Grave arXiv:0904.4184, Visser arXiv:0706.0622, Martel-Poisson gr-qc/0001069).

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

theorem ExactVacuumAtlas.Controls.Shear.pd_shear (x : Pt 4) (k i : Fin 4) :
    pd i (fun y => shear lam y k) x = jacShear lam x k i := by sorry
