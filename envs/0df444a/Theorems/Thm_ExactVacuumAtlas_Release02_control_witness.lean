-- Prove2me | Theorems.Thm_ExactVacuumAtlas_Release02_control_witness
-- name    : ExactVacuumAtlas.Release02.control_witness
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-15T21:37:52.130918+00:00
-- url     : https://prove2.me/theorems/8b3b877a-afb6-4cc5-984c-0322ec49bb51
-- title:
--   Non-vacuum control witness: a nonzero mixed Ricci component at λ = 1
-- statement:
--   Three facts at λ = 1 and the fixed point pt = (0, 1, π/4, 0) ∈ domEF: Ric(gCtl 1, giCtl 1)_{23}(pt) = √2/4; this value is ≠ 0; and the Jacobian entry jacShear 1 pt 3 2 = √2/2 (this entry differs from the identity Jacobian; a Jacobian value at one point alone does not establish non-affinity). General context (not part of this statement): R₂₃ = λ cos α sin²α vanishes exactly when λ = 0 or cos α = 0 (sin α > 0 on domEF); λ = 0 is the identity map.
-- source:
--   He Wang, Exact Vacuum Atlas II, local source snapshot (public Git repository not yet available), commit 11fb317259353b71a41d6daed466c495cffd7db4; Atlas/Release02/TransportMilestone.lean#L71-L76; SHA-256 e066de778216dc552a43e41e7967661796a78d9fd40c374cb701b56fdf9c42ae. Mathematical background: See mission/PHYSICS_BOUNDARY.md §A-F for registered definitions and literature references (Wald, Müller-Grave arXiv:0904.4184, Visser arXiv:0706.0622, Martel-Poisson gr-qc/0001069).

import Mathlib
import Definitions.Def_Atlas_Controls_CylinderTables
import Definitions.Def_Atlas_Controls_Shear
import Definitions.Def_Atlas_Controls_ShearTables
import Definitions.Def_Atlas_Core_Basic
import Definitions.Def_Atlas_Core_Certificate
import Definitions.Def_Atlas_Core_Lift
import Definitions.Def_Atlas_Core_Relation
import Definitions.Def_Atlas_Isotropic_CartChart
import Definitions.Def_Atlas_Isotropic_CartCover
import Definitions.Def_Atlas_Isotropic_CartMaps
import Definitions.Def_Atlas_Isotropic_Defs
import Definitions.Def_Atlas_Minkowski_Spherical
import Definitions.Def_Atlas_Schwarzschild_Defs
import Definitions.Def_Atlas_Schwarzschild_Domain
import Definitions.Def_Atlas_Schwarzschild_PGCertParts
import Definitions.Def_Atlas_Schwarzschild_PGDefs
import Definitions.Def_Atlas_Schwarzschild_PGRelation
import Definitions.Def_Atlas_Transport_Connection
import Definitions.Def_Atlas_Transport_Curvature
import Definitions.Def_Atlas_Transport_MatrixCalc
open Real Matrix
open ExactVacuumAtlas ExactVacuumAtlas.Schwarzschild ExactVacuumAtlas.Controls

theorem ExactVacuumAtlas.Release02.control_witness :
    ricciOf (Shear.gCtl 1) (Shear.giCtl 1) 2 3 Shear.pt = Real.sqrt 2 / 4 ∧
    ricciOf (Shear.gCtl 1) (Shear.giCtl 1) 2 3 Shear.pt ≠ 0 ∧
    Shear.jacShear 1 Shear.pt 3 2 = Real.sqrt 2 / 2 := by sorry
