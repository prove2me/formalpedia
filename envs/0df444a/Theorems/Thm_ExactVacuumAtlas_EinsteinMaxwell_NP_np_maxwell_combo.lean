-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_NP_np_maxwell_combo
-- name    : ExactVacuumAtlas.EinsteinMaxwell.NP.np_maxwell_combo
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-23T10:26:44.947119+00:00
-- url     : https://prove2.me/theorems/0b7566f1-231d-4a24-95c8-cf362a719ff2
-- title:
--   Maxwell combination with sources
-- statement:
--   Maxwell combination with sources
--
--   np_maxwell_combo_core with f = Φ₁, (D − 2ρ)Φ₁ and (δ − 2τ)Φ₁ replaced on the open set by the NP Maxwell equations with J/H sources. Source of III's res1d.
--
--   **Scope.** Exactly the hypotheses printed in the formal statement.
--
--   **中文摘要** 带源 Maxwell 组合；res1d 的来源。
-- source:
--   He Wang, Exact Spacetime Atlas V: From Linearized Einstein–Maxwell Equations to Kerr–Newman Radiation Systems. Local source, no public repository; commit b8cd107a558e153ed41fb4972ac5315499d14778; Atlas/EinsteinMaxwell/NP/NPMaxwell.lean#L450-L485; SHA-256 8db724b88398b27f6bd9e66bffe3dd4d56351f4e6b454026a2dd888370ee2a5e. Registered definitions: mission/PHYSICS_BOUNDARY.md (§K–§M); literature: P. Hintz, arXiv:2609.33661 (v1); Mark–Yang–Zimmerman–Chen, arXiv:1409.5800 (v1).

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
variable {g gi : Metric 4} {E Θ : Fin 4 → Fin 4 → Pt 4 → ℂ} {U : Set (Pt 4)}

theorem ExactVacuumAtlas.EinsteinMaxwell.NP.np_maxwell_combo (hN : NullFrameData g gi E Θ U) {F : TwoForm 4} (hFs : ∀ i j, ContDiffOn ℝ ∞ (F i j) U)
    (hFa : ∀ y ∈ U, ∀ i j, F i j y = -F j i y) {x : Pt 4} (hx : x ∈ U) :
    (fdir E 2 (fun z => (Hfr F E 0 3 2 z - Jfr g gi F Θ 1 z) / 2 + fdir E 3 (FfrF F E 0 2) z
          + (npPi g gi E Θ z - 2 * npAlpha g gi E Θ z) * phi0 E z F - npKappa g gi E Θ z * phi2 E z F) x
        + (npPiB g gi E Θ x - npBeta g gi E Θ x - npAlphaB g gi E Θ x - 2 * npTau g gi E Θ x)
          * ((Hfr F E 0 3 2 x - Jfr g gi F Θ 1 x) / 2 + fdir E 3 (FfrF F E 0 2) x
            + (npPi g gi E Θ x - 2 * npAlpha g gi E Θ x) * phi0 E x F - npKappa g gi E Θ x * phi2 E x F))
      - (fdir E 0 (fun z => (Jfr g gi F Θ 3 z + Hfr F E 1 2 0 z) / 2 + fdir E 1 (FfrF F E 0 2) z
          + (npMu g gi E Θ z - 2 * npGamma g gi E Θ z) * phi0 E z F - npSigma g gi E Θ z * phi2 E z F) x
        + (npEpsB g gi E Θ x - npEps g gi E Θ x - npRhoB g gi E Θ x - 2 * npRho g gi E Θ x)
          * ((Jfr g gi F Θ 3 x + Hfr F E 1 2 0 x) / 2 + fdir E 1 (FfrF F E 0 2) x
            + (npMu g gi E Θ x - 2 * npGamma g gi E Θ x) * phi0 E x F - npSigma g gi E Θ x * phi2 E x F))
      = 2 * phi1 E x F * (2 * psi1 g gi E x + fdir E 1 (omL g gi E Θ 0 0 2) x - fdir E 3 (omL g gi E Θ 0 2 2) x
          + (npTauB g gi E Θ x + npPi g gi E Θ x + 3 * npAlpha g gi E Θ x - npBetaB g gi E Θ x)
            * npSigma g gi E Θ x
          - (3 * npGamma g gi E Θ x + npGammaB g gi E Θ x + npMu g gi E Θ x - npMuB g gi E Θ x)
            * npKappa g gi E Θ x)
        + npKappa g gi E Θ x * fdir E 1 (fun z => phi1 E z F) x
        - npSigma g gi E Θ x * fdir E 3 (fun z => phi1 E z F) x := by sorry
