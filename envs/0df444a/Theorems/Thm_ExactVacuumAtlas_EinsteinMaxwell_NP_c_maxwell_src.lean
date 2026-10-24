-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_NP_c_maxwell_src
-- name    : ExactVacuumAtlas.EinsteinMaxwell.NP.c_maxwell_src
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-23T10:27:13.495986+00:00
-- url     : https://prove2.me/theorems/5fa24dcc-254a-4fcf-b68c-403ae7bb6cf6
-- title:
--   Complexified Maxwell combination, sources kept
-- statement:
--   Complexified Maxwell combination, sources kept
--
--   Complex combination of lin_maxwell_combo with the complexified sources cSrc1, cSrc2 kept.
--
--   **Scope.** Exactly the hypotheses printed in the formal statement.
--
--   **中文摘要** 复化 Maxwell 组合，保留源项。
-- source:
--   He Wang, Exact Spacetime Atlas V: From Linearized Einstein–Maxwell Equations to Kerr–Newman Radiation Systems. Local source, no public repository; commit b8cd107a558e153ed41fb4972ac5315499d14778; Atlas/EinsteinMaxwell/NP/V03C3.lean#L310-L329; SHA-256 1dcdc9f162705ee0e0c400be0d5f68321e834819244eb6f5b14fb12b2d5c0da3. Registered definitions: mission/PHYSICS_BOUNDARY.md (§K–§M); literature: P. Hintz, arXiv:2609.33661 (v1); Mark–Yang–Zimmerman–Chen, arXiv:1409.5800 (v1).

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
import Definitions.Def_Atlas_EinsteinMaxwell_NP_V03C3
import Definitions.Def_Atlas_EinsteinMaxwell_NP_V03Cplx
import Definitions.Def_Atlas_EinsteinMaxwell_NP_V03Family
import Definitions.Def_Atlas_EinsteinMaxwell_NP_V03LinKN
import Definitions.Def_Atlas_EinsteinMaxwell_NP_V03LinMx
import Definitions.Def_Atlas_EinsteinMaxwell_NP_V03Realize
import Definitions.Def_Atlas_EinsteinMaxwell_NP_V03Src
import Definitions.Def_Atlas_EinsteinMaxwell_NP_V03Tan
import Definitions.Def_Atlas_EinsteinMaxwell_NP_V03Var
import Definitions.Def_Atlas_EinsteinMaxwell_Variation_Defs
import Definitions.Def_Atlas_EinsteinMaxwell_Variation_Local
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
variable {M a Q : ℝ} {U : Set (Pt 4)} {τ : CTan} {x : Pt 4}
local notation "gK" => gKN M a Q
local notation "giK" => giKN M a Q
local notation "EK" => knE M a Q
local notation "ΘK" => knTh M a Q
local notation "FK" => faradayKN a Q
variable (hτ : KNCTan M a Q U τ)
include hτ

theorem ExactVacuumAtlas.EinsteinMaxwell.NP.c_maxwell_src (hx : x ∈ U) :
    fdir EK 2 (cSrc1 M a Q τ) x
        + (npPiB gK giK EK ΘK x - npBeta gK giK EK ΘK x - npAlphaB gK giK EK ΘK x - 2 * npTau gK giK EK ΘK x)
          * cSrc1 M a Q τ x
      - (fdir EK 0 (cSrc2 M a Q τ) x
        + (npEpsB gK giK EK ΘK x - npEps gK giK EK ΘK x - npRhoB gK giK EK ΘK x - 2 * npRho gK giK EK ΘK x)
          * cSrc2 M a Q τ x)
      = 2 * phi1 EK x FK * (2 * cPsi1 M a Q τ x + fdir EK 1 (cKappa M a Q τ) x - fdir EK 3 (cSigma M a Q τ) x
            + (npTauB gK giK EK ΘK x + npPi gK giK EK ΘK x + 3 * npAlpha gK giK EK ΘK x - npBetaB gK giK EK ΘK x)
              * cSigma M a Q τ x
            - (3 * npGamma gK giK EK ΘK x + npGammaB gK giK EK ΘK x + npMu gK giK EK ΘK x - npMuB gK giK EK ΘK x)
              * cKappa M a Q τ x)
        + cKappa M a Q τ x * fdir EK 1 (fun z => phi1 EK z FK) x
        - cSigma M a Q τ x * fdir EK 3 (fun z => phi1 EK z FK) x := by sorry
