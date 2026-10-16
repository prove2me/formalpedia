-- Prove2me | Theorems.Thm_ExactVacuumAtlas_Schwarzschild_Iso_domIsoCart_eq_union
-- name    : ExactVacuumAtlas.Schwarzschild.Iso.domIsoCart_eq_union
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-15T22:05:11.089307+00:00
-- url     : https://prove2.me/theorems/b5508e41-b2a2-4b60-89cc-d9ac31d136fd
-- title:
--   Covering of the natural Cartesian domain by three open pieces
-- statement:
--   For every real M: domIsoCart M = domCartSlit M ∪ (domRefl M ∪ domRot M), where domRefl M = reflX⁻¹(domCartSlit M) and domRot M = rotC⁻¹(domCartSlit M). A point with ρ > 0, ρ ≠ M/2 is off the half-plane y = 0, x ≤ 0, or (after x ↦ −x) off y = 0, x ≥ 0, or (after (x,y,z) ↦ (y,z,x)) has √(y²+z²) + y > 0; the last case covers the z-axis minus the origin.
-- source:
--   He Wang, Exact Vacuum Atlas II, local source snapshot (public Git repository not yet available), commit 11fb317259353b71a41d6daed466c495cffd7db4; Atlas/Isotropic/CartCover.lean#L185-L217; SHA-256 3d002dd52a357723e244eaf9df6b7c1eeb689295cf962455f5f09ab6ece860c8. Mathematical background: See mission/PHYSICS_BOUNDARY.md §A-F for registered definitions and literature references (Wald, Müller-Grave arXiv:0904.4184, Visser arXiv:0706.0622, Martel-Poisson gr-qc/0001069).

import Mathlib
import Definitions.Def_Atlas_Core_Basic
import Definitions.Def_Atlas_Core_Certificate
import Definitions.Def_Atlas_Core_Relation
import Definitions.Def_Atlas_Isotropic_CartChart
import Definitions.Def_Atlas_Isotropic_CartCover
import Definitions.Def_Atlas_Isotropic_CartMaps
import Definitions.Def_Atlas_Isotropic_Defs
import Definitions.Def_Atlas_Minkowski_Spherical
import Definitions.Def_Atlas_Schwarzschild_Defs
import Definitions.Def_Atlas_Schwarzschild_Domain
import Definitions.Def_Atlas_Transport_Connection
import Definitions.Def_Atlas_Transport_Curvature
import Definitions.Def_Atlas_Transport_MatrixCalc
open Real Matrix
open scoped ContDiff
open ExactVacuumAtlas ExactVacuumAtlas.Schwarzschild
open ExactVacuumAtlas
open ExactVacuumAtlas.Schwarzschild
open ExactVacuumAtlas.Schwarzschild.Iso
set_option maxHeartbeats 4000000
variable {M : ℝ}

theorem ExactVacuumAtlas.Schwarzschild.Iso.domIsoCart_eq_union (M : ℝ) : domIsoCart M = domCartSlit M ∪ (domRefl M ∪ domRot M) := by sorry
