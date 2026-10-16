-- Prove2me | Theorems.Thm_ExactVacuumAtlas_VacuumCertificate_union
-- name    : ExactVacuumAtlas.VacuumCertificate.union
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-15T21:54:44.301088+00:00
-- url     : https://prove2.me/theorems/d9845d63-e63e-4c47-9d7c-9bfe213e20cd
-- title:
--   Union of two certified domains for the same metric data
-- statement:
--   Total dimension m + 1. If (g, ĝ) carries a vacuum certificate on U₁ and on U₂, then it carries one on U₁ ∪ U₂ (openness, nonemptiness and the pointwise obligations combine; smoothness on a union of open sets).
-- source:
--   He Wang, Exact Vacuum Atlas II, local source snapshot (public Git repository not yet available), commit 11fb317259353b71a41d6daed466c495cffd7db4; Atlas/Transport/Inverse.lean#L121-L133; SHA-256 42307986732fed628bcabd660036bfa0c301394389ffa58632d43a90d35f262c. Mathematical background: See mission/PHYSICS_BOUNDARY.md §A-F for registered definitions and literature references (Wald, Müller-Grave arXiv:0904.4184, Visser arXiv:0706.0622, Martel-Poisson gr-qc/0001069).

import Mathlib
import Definitions.Def_Atlas_Core_Basic
import Definitions.Def_Atlas_Core_Certificate
import Definitions.Def_Atlas_Core_Relation
import Definitions.Def_Atlas_Transport_Connection
import Definitions.Def_Atlas_Transport_Curvature
import Definitions.Def_Atlas_Transport_MatrixCalc
open scoped ContDiff
open Matrix Filter Topology

theorem ExactVacuumAtlas.VacuumCertificate.union {m : ℕ} {g gi : Metric (m + 1)} {U₁ U₂ : Set (Pt (m + 1))}
    (h₁ : VacuumCertificate g gi U₁) (h₂ : VacuumCertificate g gi U₂) :
    VacuumCertificate g gi (U₁ ∪ U₂) := by sorry
