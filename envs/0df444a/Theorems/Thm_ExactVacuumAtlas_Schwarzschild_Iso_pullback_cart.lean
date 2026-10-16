-- Prove2me | Theorems.Thm_ExactVacuumAtlas_Schwarzschild_Iso_pullback_cart
-- name    : ExactVacuumAtlas.Schwarzschild.Iso.pullback_cart
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-15T21:59:07.499604+00:00
-- url     : https://prove2.me/theorems/c6312fb2-cc7c-488b-80d3-810cbe099f20
-- title:
--   Pull-back of the Cartesian isotropic metric under toCart
-- statement:
--   For every real M and every x with ρ = x 1 > 0: (jacCart x)ᵀ · gIsoCart M (toCart x) · jacCart x = gIso M (x). Only ρ > 0 is needed (θ, φ arbitrary).
-- source:
--   He Wang, Exact Vacuum Atlas II, local source snapshot (public Git repository not yet available), commit 11fb317259353b71a41d6daed466c495cffd7db4; Atlas/Isotropic/CartMaps.lean#L89-L104; SHA-256 19aa01acaa7bc462019d7acb24320f1f0b760ab3f42a9833c3f2e0404b8b12b1. Mathematical background: See mission/PHYSICS_BOUNDARY.md §A-F for registered definitions and literature references (Wald, Müller-Grave arXiv:0904.4184, Visser arXiv:0706.0622, Martel-Poisson gr-qc/0001069).

import Mathlib
import Definitions.Def_Atlas_Core_Basic
import Definitions.Def_Atlas_Isotropic_CartMaps
import Definitions.Def_Atlas_Isotropic_Defs
import Definitions.Def_Atlas_Schwarzschild_Defs
import Definitions.Def_Atlas_Schwarzschild_Domain
open Real Matrix
open scoped ContDiff
open ExactVacuumAtlas ExactVacuumAtlas.Schwarzschild
open ExactVacuumAtlas
open ExactVacuumAtlas.Schwarzschild
open ExactVacuumAtlas.Schwarzschild.Iso
set_option maxHeartbeats 4000000

theorem ExactVacuumAtlas.Schwarzschild.Iso.pullback_cart (M : ℝ) {x : Pt 4} (hx : 0 < x 1) :
    (jacCart x)ᵀ * metricMatrix (gIsoCart M) (toCart x) * jacCart x = metricMatrix (gIso M) x := by sorry
