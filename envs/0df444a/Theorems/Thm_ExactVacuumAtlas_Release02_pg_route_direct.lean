-- Prove2me | Theorems.Thm_ExactVacuumAtlas_Release02_pg_route_direct
-- name    : ExactVacuumAtlas.Release02.pg_route_direct
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-16T02:30:13.568891+00:00
-- url     : https://prove2.me/theorems/8039469c-1234-49d4-a1e7-a3150a5daada
-- title:
--   Painlevé–Gullstrand vacuum certificate, route 1: direct computation from generated tables
-- statement:
--   For all real M, ε with M ≥ 0 and ε² = 1: VacuumCertificate (gPG M ε) (giPG M ε) domEF. domEF = {x : 0 < x 1 ∧ 0 < x 2 ∧ x 2 < π} = {r > 0, 0 < θ < π}; x 0 (time coordinate) and x 3 (φ) arbitrary. For M > 0 the points with r = 2M belong to domEF. gPG M ε in (T, r, θ, φ): g_TT = −(1 − 2M/r), g_Tr = g_rT = ε q, g_rr = 1, g_θθ = r², g_φφ = r² sin²θ, other entries 0, q = √(2M/r); candidate inverse giPG: ĝ^TT = −1, ĝ^Tr = ĝ^rT = ε q, ĝ^rr = 1 − 2M/r, ĝ^θθ = 1/r², ĝ^φφ = 1/(r² sin²θ), other entries 0 (bundle Atlas_Schwarzschild_PGDefs). VacuumCertificate g ĝ U (bundle Atlas_Core_Certificate, release I) is the conjunction of eight obligations: U open; U nonempty; g symmetric on U; ĝ(x)·g(x) = I on U; every component of g C^∞ on U; every component of ĝ C^∞ on U; at every x ∈ U an invertible E with Eᵀ g(x) E = diag(−1,1,1,1) (Lorentzian); and all 16 components Ric(g,ĝ)_{bd}(x) = 0 for x ∈ U.
-- source:
--   He Wang, Exact Vacuum Atlas II, local source snapshot (public Git repository not yet available), commit 11fb317259353b71a41d6daed466c495cffd7db4; Atlas/Release02/TransportMilestone.lean#L51-L54; SHA-256 e066de778216dc552a43e41e7967661796a78d9fd40c374cb701b56fdf9c42ae. Mathematical background: See mission/PHYSICS_BOUNDARY.md §A-F for registered definitions and literature references (Wald, Müller-Grave arXiv:0904.4184, Visser arXiv:0706.0622, Martel-Poisson gr-qc/0001069).

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

theorem ExactVacuumAtlas.Release02.pg_route_direct : ∀ M ε : ℝ, 0 ≤ M → ε ^ 2 = 1 →
    VacuumCertificate (PG.gPG M ε) (PG.giPG M ε) domEF := by sorry
