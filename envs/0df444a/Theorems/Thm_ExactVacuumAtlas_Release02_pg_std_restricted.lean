-- Prove2me | Theorems.Thm_ExactVacuumAtlas_Release02_pg_std_restricted
-- name    : ExactVacuumAtlas.Release02.pg_std_restricted
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-16T02:32:04.551355+00:00
-- url     : https://prove2.me/theorems/ceb87147-862d-472c-bfa9-7a134a8fa6e0
-- title:
--   Standard → PG composite relation, stated on domStd M only (r ≠ 2M)
-- statement:
--   For all real M ≥ 0, ε with ε² = 1: CoordRelation (gStd M) (gPG M ε) (domStd M) (domStd M) (x ↦ pgFromEF M ε (toEF M ε x)) (z ↦ fromEF M ε (pgToEF M ε z)) (x ↦ jacInv M ε (toEF M ε x) · EFRelation.jac M ε x), with domStd M = {r > 0, r ≠ 2M, 0 < θ < π} as both source and target set. This node states ONLY the composite relation standard → PG on the standard chart (r = 2M excluded by the standard chart). The PG ↔ EF relation on all of domEF is NOT part of this node; it is conjunct (iii)/(iv) of pg_main. CoordRelation g₁ g₂ U V Φ Ψ J (bundle Atlas_Core_Relation, release I) is the conjunction of seven obligations: Ψ(Φ x) = x on U; Φ(Ψ y) = y on V; Φ maps U bijectively onto V; Φ is C^∞ on U; Ψ is C^∞ on V; every entry J(x)_{ki} is the genuine derivative of the slice u ↦ Φ(x[x_i := u])_k at u = x_i (x ∈ U); and J(x)ᵀ g₂(Φ x) J(x) = g₁(x) on U. It has no Ricci content.
-- source:
--   He Wang, Exact Vacuum Atlas II, local source snapshot (public Git repository not yet available), commit 11fb317259353b71a41d6daed466c495cffd7db4; Atlas/Release02/PGMilestone.lean#L57-L63; SHA-256 eb28ca34959afec3d4387904eae707866f8581cdbc65fb6da75141a5949df10a. Mathematical background: See mission/PHYSICS_BOUNDARY.md §A-F for registered definitions and literature references (Wald, Müller-Grave arXiv:0904.4184, Visser arXiv:0706.0622, Martel-Poisson gr-qc/0001069).

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

theorem ExactVacuumAtlas.Release02.pg_std_restricted :
    ∀ M ε : ℝ, 0 ≤ M → ε ^ 2 = 1 →
      CoordRelation (gStd M) (gPG M ε) (domStd M) (domStd M)
        (fun x => pgFromEF M ε (toEF M ε x)) (fun z => fromEF M ε (pgToEF M ε z))
        (fun x => jacInv M ε (toEF M ε x) * EFRelation.jac M ε x) := by sorry
