-- Prove2me | Theorems.Thm_ExactVacuumAtlas_Release02_isotropic_branches
-- name    : ExactVacuumAtlas.Release02.isotropic_branches
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-15T21:47:51.017997+00:00
-- url     : https://prove2.me/theorems/bc8568c6-84a7-45b1-85d9-036f1da023e7
-- title:
--   Isotropic ↔ standard Schwarzschild: the two radial branch relations
-- statement:
--   Conjunction of two statements. (i) For every real M ≥ 0: CoordRelation (gIso M) (gStd M) (domIsoOut M) (domStdExt M) (toStd M) (fromStdOut M) (jacIso M). (ii) For every real M > 0: CoordRelation (gIso M) (gStd M) (domIsoIn M) (domStdExt M) (toStd M) (fromStdIn M) (jacIso M). Here domIsoOut M = {M/2 < ρ, 0 < ρ, 0 < θ < π}, domIsoIn M = {0 < ρ < M/2, 0 < θ < π}, domStdExt M = {2M < r, 0 < r, 0 < θ < π}; fromStdOut uses ρ₊, fromStdIn uses ρ₋. CoordRelation g₁ g₂ U V Φ Ψ J (bundle Atlas_Core_Relation, release I) is the conjunction of seven obligations: Ψ(Φ x) = x on U; Φ(Ψ y) = y on V; Φ maps U bijectively onto V; Φ is C^∞ on U; Ψ is C^∞ on V; every entry J(x)_{ki} is the genuine derivative of the slice u ↦ Φ(x[x_i := u])_k at u = x_i (x ∈ U); and J(x)ᵀ g₂(Φ x) J(x) = g₁(x) on U. It has no Ricci content. Isotropic data (bundle Atlas_Isotropic_Defs): B(ρ) = 1 + M/(2ρ), A(ρ) = (1 − M/(2ρ))/B(ρ); gIso M in (t, ρ, θ, φ): g_tt = −A², g_ρρ = B⁴, g_θθ = B⁴ρ², g_φφ = B⁴ρ² sin²θ, rest 0; giIso = the reciprocal diagonal; r(ρ) = ρ(1 + M/(2ρ))² = (2ρ + M)²/(4ρ); ρ₊(r) = (r − M + √(r(r − 2M)))/2, ρ₋(r) = (r − M − √(r(r − 2M)))/2; toStd(t,ρ,θ,φ) = (t, r(ρ), θ, φ); jacIso = diag(1, 1 − M²/(4ρ²), 1, 1).
-- source:
--   He Wang, Exact Vacuum Atlas II, local source snapshot (public Git repository not yet available), commit 11fb317259353b71a41d6daed466c495cffd7db4; Atlas/Release02/TransportMilestone.lean#L78-L84; SHA-256 e066de778216dc552a43e41e7967661796a78d9fd40c374cb701b56fdf9c42ae. Mathematical background: See mission/PHYSICS_BOUNDARY.md §A-F for registered definitions and literature references (Wald, Müller-Grave arXiv:0904.4184, Visser arXiv:0706.0622, Martel-Poisson gr-qc/0001069).

import Mathlib
import Definitions.Def_Atlas_Controls_CylinderTables
import Definitions.Def_Atlas_Controls_Shear
import Definitions.Def_Atlas_Controls_ShearTables
import Definitions.Def_Atlas_Core_Basic
import Definitions.Def_Atlas_Core_Certificate
import Definitions.Def_Atlas_Core_Lift
import Definitions.Def_Atlas_Core_Relation
import Definitions.Def_Atlas_Isotropic_CartChart
import Definitions.Def_Atlas_Isotropic_CartCover
import Definitions.Def_Atlas_Isotropic_CartMaps
import Definitions.Def_Atlas_Isotropic_Defs
import Definitions.Def_Atlas_Minkowski_Spherical
import Definitions.Def_Atlas_Schwarzschild_Defs
import Definitions.Def_Atlas_Schwarzschild_Domain
import Definitions.Def_Atlas_Schwarzschild_PGCertParts
import Definitions.Def_Atlas_Schwarzschild_PGDefs
import Definitions.Def_Atlas_Schwarzschild_PGRelation
import Definitions.Def_Atlas_Transport_Connection
import Definitions.Def_Atlas_Transport_Curvature
import Definitions.Def_Atlas_Transport_MatrixCalc
open Real Matrix
open ExactVacuumAtlas ExactVacuumAtlas.Schwarzschild ExactVacuumAtlas.Controls

theorem ExactVacuumAtlas.Release02.isotropic_branches :
    (∀ M : ℝ, 0 ≤ M → CoordRelation (Iso.gIso M) (gStd M) (Iso.domIsoOut M) (Iso.domStdExt M)
      (Iso.toStd M) (Iso.fromStdOut M) (Iso.jacIso M)) ∧
    (∀ M : ℝ, 0 < M → CoordRelation (Iso.gIso M) (gStd M) (Iso.domIsoIn M) (Iso.domStdExt M)
      (Iso.toStd M) (Iso.fromStdIn M) (Iso.jacIso M)) := by sorry
