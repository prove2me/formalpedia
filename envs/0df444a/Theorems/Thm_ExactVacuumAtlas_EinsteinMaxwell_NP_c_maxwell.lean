-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_NP_c_maxwell
-- name    : ExactVacuumAtlas.EinsteinMaxwell.NP.c_maxwell
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-23T10:27:01.150437+00:00
-- url     : https://prove2.me/theorems/cba181de-178c-4190-90b7-89d7562a4871
-- title:
--   Positive (d), source-free
-- statement:
--   Positive (d), source-free
--
--   Under CLinEM and the complex gauge cPhi0 = 0 on the open U: the complexified Maxwell combination without sources (frame derivatives of the gauge vanish because the gauge holds on the open set).
--
--   **Scope.** Exactly the hypotheses printed in the formal statement.
--
--   **中文摘要** 正支 (d) 去源：CLinEM 与复规范下的 Maxwell 组合。
-- source:
--   He Wang, Exact Spacetime Atlas V: From Linearized Einstein–Maxwell Equations to Kerr–Newman Radiation Systems. Local source, no public repository; commit b8cd107a558e153ed41fb4972ac5315499d14778; Atlas/EinsteinMaxwell/NP/V03C3.lean#L477-L489; SHA-256 1dcdc9f162705ee0e0c400be0d5f68321e834819244eb6f5b14fb12b2d5c0da3. Registered definitions: mission/PHYSICS_BOUNDARY.md (§K–§M); literature: P. Hintz, arXiv:2609.33661 (v1); Mark–Yang–Zimmerman–Chen, arXiv:1409.5800 (v1).

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
variable (hL : CLinEM M a Q U τ)
include hL

theorem ExactVacuumAtlas.EinsteinMaxwell.NP.c_maxwell (hg : ∀ y ∈ U, cPhi0 M a Q τ y = 0) (hx : x ∈ U) :
    0 = 2 * phi1 EK x FK * (2 * cPsi1 M a Q τ x + fdir EK 1 (cKappa M a Q τ) x - fdir EK 3 (cSigma M a Q τ) x
            + (npTauB gK giK EK ΘK x + npPi gK giK EK ΘK x + 3 * npAlpha gK giK EK ΘK x - npBetaB gK giK EK ΘK x)
              * cSigma M a Q τ x
            - (3 * npGamma gK giK EK ΘK x + npGammaB gK giK EK ΘK x + npMu gK giK EK ΘK x - npMuB gK giK EK ΘK x)
              * cKappa M a Q τ x)
        + cKappa M a Q τ x * fdir EK 1 (fun z => phi1 EK z FK) x
        - cSigma M a Q τ x * fdir EK 3 (fun z => phi1 EK z FK) x := by sorry
