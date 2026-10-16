-- Prove2me | Theorems.Thm_ExactVacuumAtlas_Schwarzschild_Iso_cert_cart_slit
-- name    : ExactVacuumAtlas.Schwarzschild.Iso.cert_cart_slit
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-15T22:03:27.275763+00:00
-- url     : https://prove2.me/theorems/a74ff460-7e81-418d-b2f5-664033264eb5
-- title:
--   Cartesian isotropic certificate on the slit domain
-- statement:
--   For every real M ≥ 0: VacuumCertificate (gIsoCart M) (giIsoCart M) (domCartSlit M), domCartSlit M = {ρ > 0, ρ ≠ M/2, r_xy + x > 0} (the natural domain intersected with the slit condition; the radial exclusions are part of the slit domain).
-- source:
--   He Wang, Exact Vacuum Atlas II, local source snapshot (public Git repository not yet available), commit 11fb317259353b71a41d6daed466c495cffd7db4; Atlas/Isotropic/CartChart.lean#L273-L284; SHA-256 a978cca33484092eed822c5786ba958ae7ad983e09ca84ea1c69e67017f2162e. Mathematical background: See mission/PHYSICS_BOUNDARY.md §A-F for registered definitions and literature references (Wald, Müller-Grave arXiv:0904.4184, Visser arXiv:0706.0622, Martel-Poisson gr-qc/0001069).

import Mathlib
import Definitions.Def_Atlas_Core_Basic
import Definitions.Def_Atlas_Core_Certificate
import Definitions.Def_Atlas_Core_Relation
import Definitions.Def_Atlas_Isotropic_CartChart
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

theorem ExactVacuumAtlas.Schwarzschild.Iso.cert_cart_slit (hM : 0 ≤ M) :
    VacuumCertificate (gIsoCart M) (giIsoCart M) (domCartSlit M) := by sorry
