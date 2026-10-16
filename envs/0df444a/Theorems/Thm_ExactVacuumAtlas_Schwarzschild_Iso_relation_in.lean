-- Prove2me | Theorems.Thm_ExactVacuumAtlas_Schwarzschild_Iso_relation_in
-- name    : ExactVacuumAtlas.Schwarzschild.Iso.relation_in
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-15T21:43:02.476975+00:00
-- url     : https://prove2.me/theorems/accd3ede-2e2d-41d9-bacc-0e8258498e03
-- title:
--   Inner isotropic branch relation (0 < ρ < M/2 ↔ r > 2M), M > 0
-- statement:
--   For every real M > 0: CoordRelation (gIso M) (gStd M) (domIsoIn M) (domStdExt M) (toStd M) (fromStdIn M) (jacIso M) (conjunct (ii) of isotropic_branches).
-- source:
--   He Wang, Exact Vacuum Atlas II, local source snapshot (public Git repository not yet available), commit 11fb317259353b71a41d6daed466c495cffd7db4; Atlas/Isotropic/Relation.lean#L286-L296; SHA-256 7da94260c91052d64d731cd40ce965798ffa54f3a09bf2d8d615e3c5c657d5ad. Mathematical background: See mission/PHYSICS_BOUNDARY.md §A-F for registered definitions and literature references (Wald, Müller-Grave arXiv:0904.4184, Visser arXiv:0706.0622, Martel-Poisson gr-qc/0001069).

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

theorem ExactVacuumAtlas.Schwarzschild.Iso.relation_in (hM : 0 < M) :
    CoordRelation (gIso M) (gStd M) (domIsoIn M) (domStdExt M) (toStd M) (fromStdIn M) (jacIso M) := by sorry
