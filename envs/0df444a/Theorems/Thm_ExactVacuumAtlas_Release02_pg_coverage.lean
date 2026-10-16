-- Prove2me | Theorems.Thm_ExactVacuumAtlas_Release02_pg_coverage
-- name    : ExactVacuumAtlas.Release02.pg_coverage
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-16T02:29:26.670889+00:00
-- url     : https://prove2.me/theorems/c059b67f-dec5-4bc7-b9fa-625fe0ace589
-- title:
--   PG coverage root: the M = 0 case and the regular data at r = 2M for M > 0
-- statement:
--   Conjunction of three statements. (i) For every real ε (no condition ε² = 1 needed): VacuumCertificate (gPG 0 ε) (giPG 0 ε) domEF — at M = 0, q ≡ 0 and the PG data is Minkowski in spherical coordinates. (ii) For all real M > 0, ε with ε² = 1: there is x ∈ domEF with x 1 = 2M such that all 16 components Ric(gPG M ε, giPG M ε)_{bd}(x) = 0. (iii) For all real M > 0 and every real ε: equatorPt(2M) = (0, 2M, π/2, 0) ∈ domEF; q(M, 2M) = 1; the primitive H_M has derivative 1/2 at r = 2M (HasDerivAt); jac M ε (equatorPt 2M) 0 1 = ε/2; det (jac M ε (equatorPt 2M)) = 1; gPG M ε 0 0 (equatorPt 2M) = 0 and gPG M ε 0 1 (equatorPt 2M) = ε.
-- source:
--   He Wang, Exact Vacuum Atlas II, local source snapshot (public Git repository not yet available), commit 11fb317259353b71a41d6daed466c495cffd7db4; Atlas/Release02/PGMilestone.lean#L43-L55; SHA-256 eb28ca34959afec3d4387904eae707866f8581cdbc65fb6da75141a5949df10a. Mathematical background: See mission/PHYSICS_BOUNDARY.md §A-F for registered definitions and literature references (Wald, Müller-Grave arXiv:0904.4184, Visser arXiv:0706.0622, Martel-Poisson gr-qc/0001069).

import Mathlib
import Definitions.Def_Atlas_Core_Basic
import Definitions.Def_Atlas_Core_Certificate
import Definitions.Def_Atlas_Core_Lift
import Definitions.Def_Atlas_Core_Relation
import Definitions.Def_Atlas_Minkowski_Spherical
import Definitions.Def_Atlas_Schwarzschild_Defs
import Definitions.Def_Atlas_Schwarzschild_Domain
import Definitions.Def_Atlas_Schwarzschild_EFRelation
import Definitions.Def_Atlas_Schwarzschild_PGCertParts
import Definitions.Def_Atlas_Schwarzschild_PGDefs
import Definitions.Def_Atlas_Schwarzschild_PGRelation
open ExactVacuumAtlas ExactVacuumAtlas.Schwarzschild ExactVacuumAtlas.Schwarzschild.PG

theorem ExactVacuumAtlas.Release02.pg_coverage :
    (∀ ε : ℝ, VacuumCertificate (gPG 0 ε) (giPG 0 ε) domEF) ∧
    (∀ M ε : ℝ, 0 < M → ε ^ 2 = 1 →
      ∃ x ∈ domEF, x 1 = 2 * M ∧ ∀ b d, ricciOf (gPG M ε) (giPG M ε) b d x = 0) ∧
    (∀ M ε : ℝ, 0 < M →
      equatorPt (2 * M) ∈ domEF ∧ qf M (2 * M) = 1 ∧
      HasDerivAt (fun u => HPG M u) (1 / 2) (2 * M) ∧
      jac M ε (equatorPt (2 * M)) 0 1 = ε / 2 ∧ (jac M ε (equatorPt (2 * M))).det = 1 ∧
      gPG M ε 0 0 (equatorPt (2 * M)) = 0 ∧ gPG M ε 0 1 (equatorPt (2 * M)) = ε) := by sorry
