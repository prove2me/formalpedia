-- Prove2me | Theorems.Thm_ExactVacuumAtlas_Schwarzschild_Iso_pullback
-- name    : ExactVacuumAtlas.Schwarzschild.Iso.pullback
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-15T21:40:42.501607+00:00
-- url     : https://prove2.me/theorems/8a22c4f1-7fdd-4f67-8a01-1639fcc37dd8
-- title:
--   Pull-back of the standard metric under toStd
-- statement:
--   For every real M ≥ 0 and every x with ρ = x 1 > 0 and ρ ≠ M/2: (jacIso M x)ᵀ · gStd M (toStd M x) · jacIso M x = gIso M (x).
-- source:
--   He Wang, Exact Vacuum Atlas II, local source snapshot (public Git repository not yet available), commit 11fb317259353b71a41d6daed466c495cffd7db4; Atlas/Isotropic/Relation.lean#L236-L254; SHA-256 7da94260c91052d64d731cd40ce965798ffa54f3a09bf2d8d615e3c5c657d5ad. Mathematical background: See mission/PHYSICS_BOUNDARY.md §A-F for registered definitions and literature references (Wald, Müller-Grave arXiv:0904.4184, Visser arXiv:0706.0622, Martel-Poisson gr-qc/0001069).

import Mathlib
import Definitions.Def_Atlas_Core_Basic
import Definitions.Def_Atlas_Core_Relation
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
variable (M : ℝ)

theorem ExactVacuumAtlas.Schwarzschild.Iso.pullback (hM : 0 ≤ M) {x : Pt 4} (hρ : 0 < x 1) (hne : x 1 ≠ M / 2) :
    (jacIso M x)ᵀ * metricMatrix (gStd M) (toStd M x) * jacIso M x = metricMatrix (gIso M) x := by sorry
