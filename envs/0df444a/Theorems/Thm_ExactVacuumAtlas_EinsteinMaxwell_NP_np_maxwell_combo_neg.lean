-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_NP_np_maxwell_combo_neg
-- name    : ExactVacuumAtlas.EinsteinMaxwell.NP.np_maxwell_combo_neg
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-23T10:24:19.620715+00:00
-- url     : https://prove2.me/theorems/c2ded7a0-f0e9-4cdb-a53e-700efa1b5f1a
-- title:
--   Negative Maxwell combination with sources
-- statement:
--   Negative Maxwell combination with sources
--
--   Negative-branch analogue with (Δ + 2μ)Φ₁ and (δ̄ + 2π)Φ₁ replaced by the NP Maxwell equations with sources. Source of III's res1dN.
--
--   **Scope.** Exactly the hypotheses printed in the formal statement.
--
--   **中文摘要** 负支带源 Maxwell 组合；res1dN 的来源。
-- source:
--   He Wang, Exact Spacetime Atlas V: From Linearized Einstein–Maxwell Equations to Kerr–Newman Radiation Systems. Local source, no public repository; commit b8cd107a558e153ed41fb4972ac5315499d14778; Atlas/EinsteinMaxwell/NP/NPMaxwell.lean#L488-L526; SHA-256 8db724b88398b27f6bd9e66bffe3dd4d56351f4e6b454026a2dd888370ee2a5e. Registered definitions: mission/PHYSICS_BOUNDARY.md (§K–§M); literature: P. Hintz, arXiv:2609.33661 (v1); Mark–Yang–Zimmerman–Chen, arXiv:1409.5800 (v1).

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

theorem ExactVacuumAtlas.EinsteinMaxwell.NP.np_maxwell_combo_neg (hN : NullFrameData g gi E Θ U) {F : TwoForm 4} (hFs : ∀ i j, ContDiffOn ℝ ∞ (F i j) U)
    (hFa : ∀ y ∈ U, ∀ i j, F i j y = -F j i y) {x : Pt 4} (hx : x ∈ U) :
    (fdir E 3 (fun z => fdir E 2 (FfrF F E 3 1) z + npNu g gi E Θ z * phi0 E z F
          - (npTau g gi E Θ z - 2 * npBeta g gi E Θ z) * phi2 E z F - (Hfr F E 1 2 3 z - Jfr g gi F Θ 0 z) / 2) x
        + (2 * npPi g gi E Θ x + npAlpha g gi E Θ x + npBetaB g gi E Θ x - npTauB g gi E Θ x)
          * (fdir E 2 (FfrF F E 3 1) x + npNu g gi E Θ x * phi0 E x F
            - (npTau g gi E Θ x - 2 * npBeta g gi E Θ x) * phi2 E x F - (Hfr F E 1 2 3 x - Jfr g gi F Θ 0 x) / 2))
      - (fdir E 1 (fun z => fdir E 0 (FfrF F E 3 1) z + npLambda g gi E Θ z * phi0 E z F
          - (npRho g gi E Θ z - 2 * npEps g gi E Θ z) * phi2 E z F - (Jfr g gi F Θ 2 z - Hfr F E 0 1 3 z) / 2) x
        + (2 * npMu g gi E Θ x + npMuB g gi E Θ x + npGamma g gi E Θ x - npGammaB g gi E Θ x)
          * (fdir E 0 (FfrF F E 3 1) x + npLambda g gi E Θ x * phi0 E x F
            - (npRho g gi E Θ x - 2 * npEps g gi E Θ x) * phi2 E x F - (Jfr g gi F Θ 2 x - Hfr F E 0 1 3 x) / 2))
      = 2 * phi1 E x F * (2 * psi3 g gi E x + fdir E 0 (omL g gi E Θ 1 1 3) x - fdir E 2 (omL g gi E Θ 1 3 3) x
          + (npPiB g gi E Θ x + npTau g gi E Θ x + 3 * npBeta g gi E Θ x - npAlphaB g gi E Θ x)
            * npLambda g gi E Θ x
          - (3 * npEps g gi E Θ x + npEpsB g gi E Θ x + npRho g gi E Θ x - npRhoB g gi E Θ x)
            * npNu g gi E Θ x)
        - npNu g gi E Θ x * fdir E 0 (fun z => phi1 E z F) x
        + npLambda g gi E Θ x * fdir E 2 (fun z => phi1 E z F) x := by sorry
