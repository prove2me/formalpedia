-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_NP_np_ricci_c
-- name    : ExactVacuumAtlas.EinsteinMaxwell.NP.np_ricci_c
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-23T10:24:11.299649+00:00
-- url     : https://prove2.me/theorems/43d74f3d-9ad3-495a-bf5d-0cfc718f6793
-- title:
--   NP Ricci identity (4.2c), source kept
-- statement:
--   NP Ricci identity (4.2c), source kept
--
--   Dτ − Δκ = (τ + π̄)ρ + (τ̄ + π)σ + (ε − ε̄)τ − (3γ + γ̄)κ + Ψ₁ + ½R(l,m). Here barred spin-coefficient symbols denote the B-suffixed, m↔m̄ index-swapped quantities in the formal statement; numerical complex conjugacy is not assumed for a general complex frame.
--
--   **Scope.** Exactly the hypotheses printed in the formal statement.
--
--   **中文摘要** NP Ricci (4.2c)，保留源项。
-- source:
--   He Wang, Exact Spacetime Atlas V: From Linearized Einstein–Maxwell Equations to Kerr–Newman Radiation Systems. Local source, no public repository; commit b8cd107a558e153ed41fb4972ac5315499d14778; Atlas/EinsteinMaxwell/NP/NPRicci.lean#L167-L186; SHA-256 ac60d8d4c03ef192711b765ff96839ab1c7b0d06979f363abf6f01f165ba36cf. Registered definitions: mission/PHYSICS_BOUNDARY.md (§K–§M); literature: P. Hintz, arXiv:2609.33661 (v1); Mark–Yang–Zimmerman–Chen, arXiv:1409.5800 (v1).

import Mathlib
import Definitions.Def_Atlas_Core_Basic
import Definitions.Def_Atlas_Core_Lift
import Definitions.Def_Atlas_EinsteinMaxwell_Basic
import Definitions.Def_Atlas_EinsteinMaxwell_Certificate
import Definitions.Def_Atlas_EinsteinMaxwell_KN_Defs
import Definitions.Def_Atlas_EinsteinMaxwell_KN_Domain
import Definitions.Def_Atlas_EinsteinMaxwell_NP_Basic
import Definitions.Def_Atlas_EinsteinMaxwell_NP_CCalc
import Definitions.Def_Atlas_EinsteinMaxwell_NP_FrameConn
import Definitions.Def_Atlas_EinsteinMaxwell_NP_FrameNull
import Definitions.Def_Atlas_EinsteinMaxwell_NP_KNFrame
import Definitions.Def_Atlas_EinsteinMaxwell_NP_NPRicci
import Definitions.Def_Atlas_EinsteinMaxwell_NP_NPScalars
import Definitions.Def_Atlas_EinsteinMaxwell_NP_Riemann
import Definitions.Def_Atlas_Kerr_InAtoms
import Definitions.Def_Atlas_Transport_Connection
import Definitions.Def_Atlas_Transport_MatrixCalc
open scoped ContDiff Matrix
open Complex
open ExactVacuumAtlas
open ExactVacuumAtlas.EinsteinMaxwell
open ExactVacuumAtlas.EinsteinMaxwell.NP
variable {g gi : Metric 4} {E Θ : Fin 4 → Fin 4 → Pt 4 → ℂ} {U : Set (Pt 4)}

theorem ExactVacuumAtlas.EinsteinMaxwell.NP.np_ricci_c (hN : NullFrameData g gi E Θ U) {x : Pt 4} (hx : x ∈ U) :
    fdir E 0 (omL g gi E Θ 0 1 2) x - fdir E 1 (omL g gi E Θ 0 0 2) x
      = (npTau g gi E Θ x + npPiB g gi E Θ x) * npRho g gi E Θ x
        + (npTauB g gi E Θ x + npPi g gi E Θ x) * npSigma g gi E Θ x
        + (npEps g gi E Θ x - npEpsB g gi E Θ x) * npTau g gi E Θ x
        - (3 * npGamma g gi E Θ x + npGammaB g gi E Θ x) * npKappa g gi E Θ x
        + psi1 g gi E x + ricF g gi E 0 2 x / 2 := by sorry
