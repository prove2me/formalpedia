-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_NP_npKN_B
-- name    : ExactVacuumAtlas.EinsteinMaxwell.NP.npKN_B
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-23T10:25:41.381838+00:00
-- url     : https://prove2.me/theorems/e8108c92-c88c-4f4c-a09e-c920cff19f5f
-- title:
--   B-suffixed KN spin coefficients
-- statement:
--   B-suffixed KN spin coefficients
--
--   On domReg, the theorem gives the eight displayed KN background formulas for npRhoB, npTauB, npPiB, npMuB, npEpsB, npBetaB, npAlphaB and npGammaB. These are the B-suffixed, index-swapped spin coefficients; npKappaB is not one of the conclusions of this node. The theorem does not assert a numerical conjugation rule for complexified variations.
--
--   **Scope.** Exactly the hypotheses printed in the formal statement.
--
--   **中文摘要** KN 背景的八个 B 后缀系数闭式：RhoB、TauB、PiB、MuB、EpsB、BetaB、AlphaB、GammaB；本条不包含 KappaB，也不对复化扰动附加数值共轭规则。
-- source:
--   He Wang, Exact Spacetime Atlas V: From Linearized Einstein–Maxwell Equations to Kerr–Newman Radiation Systems. Local source, no public repository; commit b8cd107a558e153ed41fb4972ac5315499d14778; Atlas/EinsteinMaxwell/NP/V03Res.lean#L26-L48; SHA-256 428706d4df792e38c8711c2b24c8ab30316521cacd37941872e4003eb33e73a5. Registered definitions: mission/PHYSICS_BOUNDARY.md (§K–§M); literature: P. Hintz, arXiv:2609.33661 (v1); Mark–Yang–Zimmerman–Chen, arXiv:1409.5800 (v1).

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
import Definitions.Def_Atlas_EinsteinMaxwell_NP_V03Mode
import Definitions.Def_Atlas_EinsteinMaxwell_NP_V03Realize
import Definitions.Def_Atlas_EinsteinMaxwell_NP_V03Res
import Definitions.Def_Atlas_EinsteinMaxwell_NP_V03Src
import Definitions.Def_Atlas_EinsteinMaxwell_NP_V03Tan
import Definitions.Def_Atlas_EinsteinMaxwell_NP_V03Var
import Definitions.Def_Atlas_EinsteinMaxwell_Variation_Defs
import Definitions.Def_Atlas_EinsteinMaxwell_Variation_Local
import Definitions.Def_Atlas_Kerr_InAtoms
import Definitions.Def_Atlas_Transport_Connection
import Definitions.Def_Atlas_Transport_MatrixCalc
import Definitions.Def_Hintz2026_Chiral
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
variable {M a Q : ℝ} {x : Pt 4}

theorem ExactVacuumAtlas.EinsteinMaxwell.NP.npKN_B (hx : x ∈ domReg M a Q) :
    npRhoB (gKN M a Q) (giKN M a Q) (knE M a Q) (knTh M a Q) x = -1 / qK a x ∧
    npTauB (gKN M a Q) (giKN M a Q) (knE M a Q) (knTh M a Q) x
      = I * ((a * Real.sin (x 2) : ℝ) : ℂ) / (((Real.sqrt 2 : ℝ) : ℂ) * ((Sig a (x 1) (x 2) : ℝ) : ℂ)) ∧
    npPiB (gKN M a Q) (giKN M a Q) (knE M a Q) (knTh M a Q) x
      = -(I * ((a * Real.sin (x 2) : ℝ) : ℂ)) / (((Real.sqrt 2 : ℝ) : ℂ) * qK a x ^ 2) ∧
    npMuB (gKN M a Q) (giKN M a Q) (knE M a Q) (knTh M a Q) x
      = -((Del M a Q (x 1) : ℝ) : ℂ) / (2 * ((Sig a (x 1) (x 2) : ℝ) : ℂ) * qK a x) ∧
    npEpsB (gKN M a Q) (giKN M a Q) (knE M a Q) (knTh M a Q) x = 0 ∧
    npBetaB (gKN M a Q) (giKN M a Q) (knE M a Q) (knTh M a Q) x
      = ((Real.cos (x 2) / Real.sin (x 2) : ℝ) : ℂ) / (2 * ((Real.sqrt 2 : ℝ) : ℂ) * qbarK a x) ∧
    npAlphaB (gKN M a Q) (giKN M a Q) (knE M a Q) (knTh M a Q) x
      = -(I * ((a * Real.sin (x 2) : ℝ) : ℂ)) / (((Real.sqrt 2 : ℝ) : ℂ) * qK a x ^ 2)
        - ((Real.cos (x 2) / Real.sin (x 2) : ℝ) : ℂ) / (2 * ((Real.sqrt 2 : ℝ) : ℂ) * qK a x) ∧
    npGammaB (gKN M a Q) (giKN M a Q) (knE M a Q) (knTh M a Q) x
      = -((Del M a Q (x 1) : ℝ) : ℂ) / (2 * ((Sig a (x 1) (x 2) : ℝ) : ℂ) * qK a x)
        + (((x 1 - M) / (2 * Sig a (x 1) (x 2)) : ℝ) : ℂ) := by sorry
