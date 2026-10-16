-- Prove2me | Theorems.Thm_ExactVacuumAtlas_Release02_pg_main
-- name    : ExactVacuumAtlas.Release02.pg_main
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-16T02:30:20.255679+00:00
-- url     : https://prove2.me/theorems/c7a58504-85ea-42cb-bda2-af036f83da68
-- title:
--   PG milestone root: both PG certificates and the PG ↔ EF relations in both directions on all of domEF
-- statement:
--   Conjunction of four statements. (i) For every real M ≥ 0: VacuumCertificate (gPG M 1) (giPG M 1) domEF. (ii) For every real M ≥ 0: VacuumCertificate (gPG M (−1)) (giPG M (−1)) domEF. (iii) For all real M ≥ 0, ε with ε² = 1: CoordRelation (gPG M ε) (gEF M ε) domEF domEF (pgToEF M ε) (pgFromEF M ε) (jac M ε). (iv) For all real M ≥ 0, ε with ε² = 1: CoordRelation (gEF M ε) (gPG M ε) domEF domEF (pgFromEF M ε) (pgToEF M ε) (jacInv M ε). Here pgToEF(T,r,θ,φ) = (T + ε H_M(r), r, θ, φ), H_M(r) = r − 2√(2M)√r + 4M log(√r + √(2M)) (H_M′ = 1/(1 + q)), pgFromEF its inverse, jac = I + (ε/(1+q)) E₀₁, jacInv = I − (ε/(1+q)) E₀₁ (det 1); gEF M ε is the release-I Eddington–Finkelstein family with the same ε (w = v for ε = 1, w = u for ε = −1). Both relations hold on the whole of domEF = {x : 0 < x 1 ∧ 0 < x 2 ∧ x 2 < π} = {r > 0, 0 < θ < π}; x 0 (time coordinate) and x 3 (φ) arbitrary — the points r = 2M (M > 0) are not excluded. gPG M ε in (T, r, θ, φ): g_TT = −(1 − 2M/r), g_Tr = g_rT = ε q, g_rr = 1, g_θθ = r², g_φφ = r² sin²θ, other entries 0, q = √(2M/r); candidate inverse giPG: ĝ^TT = −1, ĝ^Tr = ĝ^rT = ε q, ĝ^rr = 1 − 2M/r, ĝ^θθ = 1/r², ĝ^φφ = 1/(r² sin²θ), other entries 0 (bundle Atlas_Schwarzschild_PGDefs). VacuumCertificate g ĝ U (bundle Atlas_Core_Certificate, release I) is the conjunction of eight obligations: U open; U nonempty; g symmetric on U; ĝ(x)·g(x) = I on U; every component of g C^∞ on U; every component of ĝ C^∞ on U; at every x ∈ U an invertible E with Eᵀ g(x) E = diag(−1,1,1,1) (Lorentzian); and all 16 components Ric(g,ĝ)_{bd}(x) = 0 for x ∈ U. CoordRelation g₁ g₂ U V Φ Ψ J (bundle Atlas_Core_Relation, release I) is the conjunction of seven obligations: Ψ(Φ x) = x on U; Φ(Ψ y) = y on V; Φ maps U bijectively onto V; Φ is C^∞ on U; Ψ is C^∞ on V; every entry J(x)_{ki} is the genuine derivative of the slice u ↦ Φ(x[x_i := u])_k at u = x_i (x ∈ U); and J(x)ᵀ g₂(Φ x) J(x) = g₁(x) on U. It has no Ricci content.
-- source:
--   He Wang, Exact Vacuum Atlas II, local source snapshot (public Git repository not yet available), commit 11fb317259353b71a41d6daed466c495cffd7db4; Atlas/Release02/PGMilestone.lean#L31-L41; SHA-256 eb28ca34959afec3d4387904eae707866f8581cdbc65fb6da75141a5949df10a. Mathematical background: See mission/PHYSICS_BOUNDARY.md §A-F for registered definitions and literature references (Wald, Müller-Grave arXiv:0904.4184, Visser arXiv:0706.0622, Martel-Poisson gr-qc/0001069).

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

theorem ExactVacuumAtlas.Release02.pg_main :
    (∀ M : ℝ, 0 ≤ M → VacuumCertificate (gPG M 1) (giPG M 1) domEF) ∧
    (∀ M : ℝ, 0 ≤ M → VacuumCertificate (gPG M (-1)) (giPG M (-1)) domEF) ∧
    (∀ M ε : ℝ, 0 ≤ M → ε ^ 2 = 1 →
      CoordRelation (gPG M ε) (gEF M ε) domEF domEF (pgToEF M ε) (pgFromEF M ε) (jac M ε)) ∧
    (∀ M ε : ℝ, 0 ≤ M → ε ^ 2 = 1 →
      CoordRelation (gEF M ε) (gPG M ε) domEF domEF (pgFromEF M ε) (pgToEF M ε) (jacInv M ε)) := by sorry
