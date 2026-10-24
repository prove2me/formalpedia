-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_NP_lin_ricci_j
-- name    : ExactVacuumAtlas.EinsteinMaxwell.NP.lin_ricci_j
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-23T10:24:59.750386+00:00
-- url     : https://prove2.me/theorems/2a565c19-fae3-4806-8803-0da486e9b875
-- title:
--   Linearised NP Ricci (4.2j) at KN
-- statement:
--   Linearised NP Ricci (4.2j) at KN
--
--   Δ δ(omL 1 3 3) − δ̄ δ(omL 1 1 3) = δλ(μ + μ̄ + 3γ − γ̄) − δν(π − τ̄ + β̄ + 3α) + δΨ₄ with KN coefficients (source of res1cN).
--
--   **Scope.** Exactly the hypotheses printed in the formal statement.
--
--   **中文摘要** KN 处线性化 Ricci (4.2j)。
-- source:
--   He Wang, Exact Spacetime Atlas V: From Linearized Einstein–Maxwell Equations to Kerr–Newman Radiation Systems. Local source, no public repository; commit b8cd107a558e153ed41fb4972ac5315499d14778; Atlas/EinsteinMaxwell/NP/V03LinKN.lean#L444-L482; SHA-256 9c8ef1119adf30602b657e281877a44735f55b9af3e5d202336d742bdd8d3197. Registered definitions: mission/PHYSICS_BOUNDARY.md (§K–§M); literature: P. Hintz, arXiv:2609.33661 (v1); Mark–Yang–Zimmerman–Chen, arXiv:1409.5800 (v1).

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
import Definitions.Def_Atlas_EinsteinMaxwell_NP_KNComm
import Definitions.Def_Atlas_EinsteinMaxwell_NP_KNFaraday
import Definitions.Def_Atlas_EinsteinMaxwell_NP_KNFrame
import Definitions.Def_Atlas_EinsteinMaxwell_NP_KNSpin
import Definitions.Def_Atlas_EinsteinMaxwell_NP_KNWeyl
import Definitions.Def_Atlas_EinsteinMaxwell_NP_ModeOperators
import Definitions.Def_Atlas_EinsteinMaxwell_NP_NPBianchi
import Definitions.Def_Atlas_EinsteinMaxwell_NP_NPMaxwell
import Definitions.Def_Atlas_EinsteinMaxwell_NP_NPRicci
import Definitions.Def_Atlas_EinsteinMaxwell_NP_NPScalars
import Definitions.Def_Atlas_EinsteinMaxwell_NP_Riemann
import Definitions.Def_Atlas_EinsteinMaxwell_NP_V03Family
import Definitions.Def_Atlas_EinsteinMaxwell_NP_V03LinKN
import Definitions.Def_Atlas_EinsteinMaxwell_NP_V03Realize
import Definitions.Def_Atlas_EinsteinMaxwell_NP_V03Var
import Definitions.Def_Atlas_EinsteinMaxwell_Variation_Defs
import Definitions.Def_Atlas_Kerr_InAtoms
import Definitions.Def_Atlas_Transport_Connection
import Definitions.Def_Atlas_Transport_MatrixCalc
import Definitions.Def_Hintz2026_Core
import Definitions.Def_Hintz2026_Domain
import Definitions.Def_Hintz2026_System1
import Definitions.Def_Hintz2026_System4
open Complex Filter Topology
open scoped ComplexConjugate Matrix ContDiff
open ExactVacuumAtlas.EinsteinMaxwell ExactVacuumAtlas.Variation
open ExactVacuumAtlas.EinsteinMaxwell.KN (Sig Del gKN giKN domReg domKN faradayKN)
open ExactVacuumAtlas
open ExactVacuumAtlas.EinsteinMaxwell
open ExactVacuumAtlas.EinsteinMaxwell.NP
variable {M a Q : ℝ} {g gi : ℝ → Metric 4} {F : ℝ → TwoForm 4} {E Θ : ℝ → Fin 4 → Fin 4 → Pt 4 → ℂ}
  {W : Set (ℝ × Pt 4)} {h : Metric 4} {f : TwoForm 4} {B : Fin 4 → Fin 4 → Pt 4 → ℂ}
local notation "gK" => gKN M a Q
local notation "giK" => giKN M a Q
local notation "EK" => knE M a Q
local notation "ΘK" => knTh M a Q

theorem ExactVacuumAtlas.EinsteinMaxwell.NP.lin_ricci_j (hK : KNFam M a Q g gi F E Θ W) (ht : NPTangent g F E W h f B) {x : Pt 4}
    (hx0 : ((0 : ℝ), x) ∈ W) :
    fdir EK 1 (fun y => omLVar gK h EK B 1 3 3 y) x - fdir EK 3 (fun y => omLVar gK h EK B 1 1 3 y) x
      = lambdaVar gK h EK B x * (npMu gK giK EK ΘK x + npMuB gK giK EK ΘK x + 3 * npGamma gK giK EK ΘK x
          - npGammaB gK giK EK ΘK x)
        - nuVar gK h EK B x * (npPi gK giK EK ΘK x - npTauB gK giK EK ΘK x + npBetaB gK giK EK ΘK x
          + 3 * npAlpha gK giK EK ΘK x)
        + psi4Var gK giK h EK B x := by sorry
