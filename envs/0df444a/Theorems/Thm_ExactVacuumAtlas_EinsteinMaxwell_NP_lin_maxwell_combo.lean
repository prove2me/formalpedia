-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_NP_lin_maxwell_combo
-- name    : ExactVacuumAtlas.EinsteinMaxwell.NP.lin_maxwell_combo
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-23T10:26:50.318805+00:00
-- url     : https://prove2.me/theorems/1fe1a106-e2d7-4f44-ae6d-75803d5279aa
-- title:
--   Linearised Maxwell combination at KN, sources kept
-- statement:
--   Linearised Maxwell combination at KN, sources kept
--
--   Linearise the sourced Maxwell combination at KN along the stated NPTangent. Write D_A = fdir EK A, S₁⁽¹⁾ = srcS1, S₂⁽¹⁾ = srcS2, κ₁ = kappaVar, σ₁ = sigmaVar and Ψ₁⁽¹⁾ = psi1Var. With the background coefficients X = π_B − β − α_B − 2τ, Y = ε_B − ε − ρ_B − 2ρ, A₀ = τ_B + π + 3α − β_B and B₀ = 3γ + γ_B + μ − μ_B, the identity is (D₂ + X)S₁⁽¹⁾ − (D₀ + Y)S₂⁽¹⁾ = 2Φ₁(2Ψ₁⁽¹⁾ + D₁κ₁ − D₃σ₁ + A₀σ₁ − B₀κ₁) + κ₁D₁Φ₁ − σ₁D₃Φ₁. Φ₁ is the background phi1 EK FK. The first direction is D₂ (along m), not D₃ (along m̄); the two background-derivative terms are retained. Maxwell source variations have not yet been set to zero.
--
--   **Scope.** Exactly the hypotheses printed in the formal statement.
--
--   **中文摘要** KN 处保留源项的线性化 Maxwell 组合。左端第一项沿 m（D₂）求导，不是沿 m̄（D₃）；右端保留 κ₁D₁Φ₁−σ₁D₃Φ₁，其中 Φ₁ 是背景 Coulomb 分量。
-- source:
--   He Wang, Exact Spacetime Atlas V: From Linearized Einstein–Maxwell Equations to Kerr–Newman Radiation Systems. Local source, no public repository; commit b8cd107a558e153ed41fb4972ac5315499d14778; Atlas/EinsteinMaxwell/NP/V03LinMx.lean#L250-L336; SHA-256 70faf22e9e83692c79cdd87754cd04e53ebf59f983c055f9a9013fa7752bb600. Registered definitions: mission/PHYSICS_BOUNDARY.md (§K–§M); literature: P. Hintz, arXiv:2609.33661 (v1); Mark–Yang–Zimmerman–Chen, arXiv:1409.5800 (v1).

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
import Definitions.Def_Atlas_EinsteinMaxwell_NP_V03LinMx
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
local notation "FK" => faradayKN a Q

theorem ExactVacuumAtlas.EinsteinMaxwell.NP.lin_maxwell_combo (hK : KNFam M a Q g gi F E Θ W) (ht : NPTangent g F E W h f B) {x : Pt 4}
    (hx0 : ((0 : ℝ), x) ∈ W) :
    fdir EK 2 (srcS1 FK f gK giK h EK ΘK B) x
        + (npPiB gK giK EK ΘK x - npBeta gK giK EK ΘK x - npAlphaB gK giK EK ΘK x - 2 * npTau gK giK EK ΘK x)
          * srcS1 FK f gK giK h EK ΘK B x
      - (fdir EK 0 (srcS2 FK f gK giK h EK ΘK B) x
        + (npEpsB gK giK EK ΘK x - npEps gK giK EK ΘK x - npRhoB gK giK EK ΘK x - 2 * npRho gK giK EK ΘK x)
          * srcS2 FK f gK giK h EK ΘK B x)
      = 2 * phi1 EK x FK * (2 * psi1Var gK giK h EK B x + fdir EK 1 (kappaVar gK h EK B) x
            - fdir EK 3 (sigmaVar gK h EK B) x
            + (npTauB gK giK EK ΘK x + npPi gK giK EK ΘK x + 3 * npAlpha gK giK EK ΘK x - npBetaB gK giK EK ΘK x)
              * sigmaVar gK h EK B x
            - (3 * npGamma gK giK EK ΘK x + npGammaB gK giK EK ΘK x + npMu gK giK EK ΘK x - npMuB gK giK EK ΘK x)
              * kappaVar gK h EK B x)
        + kappaVar gK h EK B x * fdir EK 1 (fun z => phi1 EK z FK) x
        - sigmaVar gK h EK B x * fdir EK 3 (fun z => phi1 EK z FK) x := by sorry
