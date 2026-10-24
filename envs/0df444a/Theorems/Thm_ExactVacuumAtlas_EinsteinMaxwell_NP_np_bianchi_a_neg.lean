-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_NP_np_bianchi_a_neg
-- name    : ExactVacuumAtlas.EinsteinMaxwell.NP.np_bianchi_a_neg
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-23T10:22:07.110278+00:00
-- url     : https://prove2.me/theorems/e4342724-72f2-496b-9f29-7726cf8adf05
-- title:
--   Negative-branch NP Bianchi identity (GHP prime of (a)) with Ricci sources
-- statement:
--   Negative-branch NP Bianchi identity (GHP prime of (a)) with Ricci sources
--
--   Companion of milestone 6 for the negative branch: for any null frame with NullFrameData, the GHP-primed identity −Δ Ψ₃ + δ Ψ₄ + ½ Δ R(n,m̄) − ½ δ̄ R(n,n) = 2Ψ₃γ + 4Ψ₃μ − 3Ψ₂ν − 4Ψ₄β + Ψ₄τ + (Ricci source terms as printed). Geometric source of III's res1aN.
--
--   **Scope.** General null frame on an open set; no field equation.
--
--   **中文摘要** 负支 NP Bianchi 恒等式（(a) 的 GHP 撇），保留 Ricci 源项；III 的 res1aN 的来源。
-- source:
--   He Wang, Exact Spacetime Atlas V: From Linearized Einstein–Maxwell Equations to Kerr–Newman Radiation Systems. Local source, no public repository; commit b8cd107a558e153ed41fb4972ac5315499d14778; Atlas/EinsteinMaxwell/NP/NPBianchiNP.lean#L486-L521; SHA-256 ea0382ebea92c4638a3d050ceb9e7891f3c8fee12cfa1baecd44232265e2ddb3. Registered definitions: mission/PHYSICS_BOUNDARY.md (§K–§M); literature: P. Hintz, arXiv:2609.33661 (v1); Mark–Yang–Zimmerman–Chen, arXiv:1409.5800 (v1).

import Mathlib
import Definitions.Def_Atlas_Core_Basic
import Definitions.Def_Atlas_Core_Lift
import Definitions.Def_Atlas_EinsteinMaxwell_Basic
import Definitions.Def_Atlas_EinsteinMaxwell_Certificate
import Definitions.Def_Atlas_EinsteinMaxwell_KN_Defs
import Definitions.Def_Atlas_EinsteinMaxwell_KN_Domain
import Definitions.Def_Atlas_EinsteinMaxwell_NP_Basic
import Definitions.Def_Atlas_EinsteinMaxwell_NP_Bianchi
import Definitions.Def_Atlas_EinsteinMaxwell_NP_CCalc
import Definitions.Def_Atlas_EinsteinMaxwell_NP_FrameConn
import Definitions.Def_Atlas_EinsteinMaxwell_NP_FrameNull
import Definitions.Def_Atlas_EinsteinMaxwell_NP_KNFrame
import Definitions.Def_Atlas_EinsteinMaxwell_NP_NPBianchi
import Definitions.Def_Atlas_EinsteinMaxwell_NP_NPMaxwell
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
set_option linter.unusedSimpArgs false
variable {g gi : Metric 4} {E Θ : Fin 4 → Fin 4 → Pt 4 → ℂ} {U : Set (Pt 4)}

theorem ExactVacuumAtlas.EinsteinMaxwell.NP.np_bianchi_a_neg (hN : NullFrameData g gi E Θ U) {x : Pt 4} (hx : x ∈ U) :
    (-1) * fdir E 1 (psi3 g gi E) x +
        (1) * fdir E 2 (psi4 g gi E) x +
        (1/2) * fdir E 1 (ricF g gi E 1 3) x +
        (-1/2) * fdir E 3 (ricF g gi E 1 1) x
      = (2) * psi3 g gi E x * npGamma g gi E Θ x +
        (4) * psi3 g gi E x * npMu g gi E Θ x +
        (-3) * psi2 g gi E x * npNu g gi E Θ x +
        (-4) * psi4 g gi E x * npBeta g gi E Θ x +
        (1) * psi4 g gi E x * npTau g gi E Θ x +
        (1) * npAlpha g gi E Θ x * ricF g gi E 1 1 x +
        (1) * npBetaB g gi E Θ x * ricF g gi E 1 1 x +
        (-1) * npGamma g gi E Θ x * ricF g gi E 1 3 x +
        (-1) * npLambda g gi E Θ x * ricF g gi E 1 2 x +
        (-1) * npMuB g gi E Θ x * ricF g gi E 1 3 x +
        (1/2) * npNu g gi E Θ x * ricF g gi E 0 1 x +
        (1/2) * npNu g gi E Θ x * ricF g gi E 2 3 x +
        (1/2) * npNuB g gi E Θ x * ricF g gi E 3 3 x +
        (-1/2) * ricF g gi E 1 1 x * npTauB g gi E Θ x := by sorry
