-- Prove2me | Theorems.Thm_ExactVacuumAtlas_Release02_isotropic_sph_cart_relation
-- name    : ExactVacuumAtlas.Release02.isotropic_sph_cart_relation
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-15T22:31:58.234051+00:00
-- url     : https://prove2.me/theorems/c51d79cc-1984-4d8d-96ac-46f14651bd8d
-- title:
--   Spherical ↔ Cartesian isotropic chart relation on the slit chart (every real M)
-- statement:
--   For every real M (no sign condition): CoordRelation (gIso M) (gIsoCart M) (domIsoChart M) (domCartSlit M) toCart fromCart jacCart, where domIsoChart M = domIso M ∩ {−π < φ < π}, domCartSlit M = {y : 0 < ρ(y) ∧ ρ(y) ≠ M/2 ∧ 0 < r_xy(y) + y 1}, ρ(y) = √(x²+y²+z²), r_xy = √(x²+y²), (x,y,z) = (y 1, y 2, y 3); toCart(t,ρ,θ,φ) = (t, ρ sin θ cos φ, ρ sin θ sin φ, ρ cos θ); fromCart(t,x,y,z) = (t, ρ, arccos(z/ρ), 2 arctan(y/(r_xy + x))); jacCart is the explicit 4×4 Jacobian (det = ρ² sin θ); gIsoCart M: g_tt = −A(ρ)², g_xx = g_yy = g_zz = B(ρ)⁴. CoordRelation g₁ g₂ U V Φ Ψ J (bundle Atlas_Core_Relation, release I) is the conjunction of seven obligations: Ψ(Φ x) = x on U; Φ(Ψ y) = y on V; Φ maps U bijectively onto V; Φ is C^∞ on U; Ψ is C^∞ on V; every entry J(x)_{ki} is the genuine derivative of the slice u ↦ Φ(x[x_i := u])_k at u = x_i (x ∈ U); and J(x)ᵀ g₂(Φ x) J(x) = g₁(x) on U. It has no Ricci content.
-- source:
--   He Wang, Exact Vacuum Atlas II, local source snapshot (public Git repository not yet available), commit 11fb317259353b71a41d6daed466c495cffd7db4; Atlas/Release02/TransportMilestone.lean#L90-L94; SHA-256 e066de778216dc552a43e41e7967661796a78d9fd40c374cb701b56fdf9c42ae. Mathematical background: See mission/PHYSICS_BOUNDARY.md §A-F for registered definitions and literature references (Wald, Müller-Grave arXiv:0904.4184, Visser arXiv:0706.0622, Martel-Poisson gr-qc/0001069).

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

theorem ExactVacuumAtlas.Release02.isotropic_sph_cart_relation : ∀ M : ℝ,
    CoordRelation (Iso.gIso M) (Iso.gIsoCart M) (Iso.domIsoChart M) (Iso.domCartSlit M)
      Iso.toCart Iso.fromCart Iso.jacCart := by sorry
