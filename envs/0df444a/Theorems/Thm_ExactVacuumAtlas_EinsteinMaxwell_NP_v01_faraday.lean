-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_NP_v01_faraday
-- name    : ExactVacuumAtlas.EinsteinMaxwell.NP.v01_faraday
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-23T10:26:42.876373+00:00
-- url     : https://prove2.me/theorems/4ad5978a-d7d1-43a9-bdb6-0e2fdc261968
-- title:
--   Kerr–Newman Faraday frame projections and the Coulomb component Φ₁ = Q/(2q̄²)
-- statement:
--   Kerr–Newman Faraday frame projections and the Coulomb component Φ₁ = Q/(2q̄²)
--
--   For every real M, a, Q and x ∈ domReg: the bilinear frame projections of IV's faradayKN a Q are F(l,n) = Q(r² − a² cos²θ)/Σ², F(m,m̄) = −2i Q a r cos θ/Σ², F(l,m) = F(l,m̄) = F(n,m) = F(n,m̄) = 0; hence Φ₀ = phi0K = 0, Φ₂ = phi2K = 0 and Φ₁ = phiC = Q/(2 q̄²), with phiC = 0 ↔ Q = 0.
--
--   **Scope.** Every real M, a, Q; points of domReg.
--
--   **中文摘要** IV 的 KN Faraday 场在 Kinnersley 标架上的投影：Φ₀=Φ₂=0，Φ₁=Q/(2q̄²)，且 Φ₁=0 当且仅当 Q=0。
-- source:
--   He Wang, Exact Spacetime Atlas V: From Linearized Einstein–Maxwell Equations to Kerr–Newman Radiation Systems. Local source, no public repository; commit b8cd107a558e153ed41fb4972ac5315499d14778; Atlas/EinsteinMaxwell/NP/V01.lean#L30-L44; SHA-256 163c0780f59c9198d1097ef71bf5f7b6a5671f5ab3e49027f671fc9cbbb4a34a. Registered definitions: mission/PHYSICS_BOUNDARY.md (§K–§M); literature: P. Hintz, arXiv:2609.33661 (v1); Mark–Yang–Zimmerman–Chen, arXiv:1409.5800 (v1).

import Mathlib
import Definitions.Def_Atlas_Core_Basic
import Definitions.Def_Atlas_Core_Lift
import Definitions.Def_Atlas_EinsteinMaxwell_Basic
import Definitions.Def_Atlas_EinsteinMaxwell_Certificate
import Definitions.Def_Atlas_EinsteinMaxwell_KN_Defs
import Definitions.Def_Atlas_EinsteinMaxwell_KN_Domain
import Definitions.Def_Atlas_EinsteinMaxwell_NP_Basic
import Definitions.Def_Atlas_EinsteinMaxwell_NP_KNFaraday
import Definitions.Def_Atlas_EinsteinMaxwell_NP_KNFrame
import Definitions.Def_Atlas_EinsteinMaxwell_NP_ModeOperators
import Definitions.Def_Atlas_Kerr_InAtoms
import Definitions.Def_Hintz2026_Core
import Definitions.Def_Hintz2026_Domain
import Definitions.Def_Hintz2026_System1
import Definitions.Def_Hintz2026_System4
open Real
open scoped ComplexConjugate Matrix ContDiff
open ExactVacuumAtlas.EinsteinMaxwell.KN (gKN giKN faradayKN domReg domKN)

theorem ExactVacuumAtlas.EinsteinMaxwell.NP.v01_faraday (M a Q : ℝ) {x : Pt 4} (hx : x ∈ domReg M a Q) :
    ccontr (faradayKN a Q) x (knL M a Q x) (knN M a Q x) =
        ((Q * (x 1 ^ 2 - a ^ 2 * cos (x 2) ^ 2) / KN.Sig a (x 1) (x 2) ^ 2 : ℝ) : ℂ) ∧
      ccontr (faradayKN a Q) x (knM a x) (knMbar a x) =
        -(2 * Complex.I * ((Q * a * x 1 * cos (x 2) / KN.Sig a (x 1) (x 2) ^ 2 : ℝ) : ℂ)) ∧
      ccontr (faradayKN a Q) x (knL M a Q x) (knM a x) = 0 ∧
      ccontr (faradayKN a Q) x (knL M a Q x) (knMbar a x) = 0 ∧
      ccontr (faradayKN a Q) x (knN M a Q x) (knM a x) = 0 ∧
      ccontr (faradayKN a Q) x (knN M a Q x) (knMbar a x) = 0 ∧
      phi0K M a Q x = 0 ∧ phi2K M a Q x = 0 ∧
      phiC M a Q x = (Q : ℂ) / (2 * qbarK a x ^ 2) ∧ (phiC M a Q x = 0 ↔ Q = 0) := by sorry
