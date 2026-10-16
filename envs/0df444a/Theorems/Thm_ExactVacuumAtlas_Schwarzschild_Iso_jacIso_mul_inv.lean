-- Prove2me | Theorems.Thm_ExactVacuumAtlas_Schwarzschild_Iso_jacIso_mul_inv
-- name    : ExactVacuumAtlas.Schwarzschild.Iso.jacIso_mul_inv
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-15T21:52:59.341703+00:00
-- url     : https://prove2.me/theorems/35084b2b-065e-4b6a-bad7-40e5c63f95e9
-- title:
--   jacIso · jacIsoInv = I away from ρ = 0, ±M/2
-- statement:
--   For every real M and every x with x 1 ≠ 0, x 1 ≠ M/2 and x 1 ≠ −M/2: jacIso M x · jacIsoInv M x = I (the radial entry 1 − M²/(4ρ²) is nonzero exactly there).
-- source:
--   He Wang, Exact Vacuum Atlas II, local source snapshot (public Git repository not yet available), commit 11fb317259353b71a41d6daed466c495cffd7db4; Atlas/Isotropic/Relation.lean#L204-L217; SHA-256 7da94260c91052d64d731cd40ce965798ffa54f3a09bf2d8d615e3c5c657d5ad. Mathematical background: See mission/PHYSICS_BOUNDARY.md §A-F for registered definitions and literature references (Wald, Müller-Grave arXiv:0904.4184, Visser arXiv:0706.0622, Martel-Poisson gr-qc/0001069).

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

theorem ExactVacuumAtlas.Schwarzschild.Iso.jacIso_mul_inv {x : Pt 4} (hr : x 1 ≠ 0) (hne : x 1 ≠ M / 2) (hne' : x 1 ≠ -(M / 2)) :
    jacIso M x * jacIsoInv M x = 1 := by sorry
