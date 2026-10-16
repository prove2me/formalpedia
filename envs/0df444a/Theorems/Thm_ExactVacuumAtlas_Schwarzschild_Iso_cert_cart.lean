-- Prove2me | Theorems.Thm_ExactVacuumAtlas_Schwarzschild_Iso_cert_cart
-- name    : ExactVacuumAtlas.Schwarzschild.Iso.cert_cart
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-15T22:07:29.089894+00:00
-- url     : https://prove2.me/theorems/bf00fe44-1f46-4f54-aab7-58c8655352d4
-- title:
--   Cartesian isotropic certificate on the natural domain {ρ > 0, ρ ≠ M/2}
-- statement:
--   For every real M ≥ 0: VacuumCertificate (gIsoCart M) (giIsoCart M) (domIsoCart M) (the statement wrapped by isotropic_cartesian).
-- source:
--   He Wang, Exact Vacuum Atlas II, local source snapshot (public Git repository not yet available), commit 11fb317259353b71a41d6daed466c495cffd7db4; Atlas/Isotropic/CartCover.lean#L219-L223; SHA-256 3d002dd52a357723e244eaf9df6b7c1eeb689295cf962455f5f09ab6ece860c8. Mathematical background: See mission/PHYSICS_BOUNDARY.md §A-F for registered definitions and literature references (Wald, Müller-Grave arXiv:0904.4184, Visser arXiv:0706.0622, Martel-Poisson gr-qc/0001069).

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

theorem ExactVacuumAtlas.Schwarzschild.Iso.cert_cart (hM : 0 ≤ M) : VacuumCertificate (gIsoCart M) (giIsoCart M) (domIsoCart M) := by sorry
