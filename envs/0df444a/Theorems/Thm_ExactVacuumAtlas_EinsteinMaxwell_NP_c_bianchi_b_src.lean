-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_NP_c_bianchi_b_src
-- name    : ExactVacuumAtlas.EinsteinMaxwell.NP.c_bianchi_b_src
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-23T10:24:47.385766+00:00
-- url     : https://prove2.me/theorems/5aec25f7-1e84-40fb-a114-055953be4ce3
-- title:
--   Complexified linearised Bianchi (b), sources kept
-- statement:
--   Complexified linearised Bianchi (b), sources kept
--
--   As c_bianchi_a_src for (b).
--
--   **Scope.** Exactly the hypotheses printed in the formal statement.
--
--   **中文摘要** 复化线性化 Bianchi (b)，保留源项。
-- source:
--   He Wang, Exact Spacetime Atlas V: From Linearized Einstein–Maxwell Equations to Kerr–Newman Radiation Systems. Local source, no public repository; commit b8cd107a558e153ed41fb4972ac5315499d14778; Atlas/EinsteinMaxwell/NP/V03C3.lean#L260-L274; SHA-256 1dcdc9f162705ee0e0c400be0d5f68321e834819244eb6f5b14fb12b2d5c0da3. Registered definitions: mission/PHYSICS_BOUNDARY.md (§K–§M); literature: P. Hintz, arXiv:2609.33661 (v1); Mark–Yang–Zimmerman–Chen, arXiv:1409.5800 (v1).

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

theorem ExactVacuumAtlas.EinsteinMaxwell.NP.c_bianchi_b_src (hx : x ∈ U) :
    fdir EK 1 (cPsi0 M a Q τ) x - fdir EK 2 (cPsi1 M a Q τ) x
        + (1/2) * fdir EK 0 (cRicF M a Q τ 2 2) x - (1/2) * fdir EK 2 (cRicF M a Q τ 0 2) x
      = (-2 * npBeta gK giK EK ΘK x - 4 * npTau gK giK EK ΘK x) * cPsi1 M a Q τ x
        + (4 * npGamma gK giK EK ΘK x - npMu gK giK EK ΘK x) * cPsi0 M a Q τ x
        + (3 * psi2 gK giK EK x + (1/2) * ricF gK giK EK 0 1 x + (1/2) * ricF gK giK EK 2 3 x)
          * cSigma M a Q τ x
        + (npPiB gK giK EK ΘK x - npBeta gK giK EK ΘK x) * cRicF M a Q τ 0 2 x
        + (1/2) * npRhoB gK giK EK ΘK x * cRicF M a Q τ 2 2 x := by sorry
