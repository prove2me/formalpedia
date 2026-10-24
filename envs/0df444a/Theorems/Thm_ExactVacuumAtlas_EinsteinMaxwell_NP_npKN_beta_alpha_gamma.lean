-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_NP_npKN_beta_alpha_gamma
-- name    : ExactVacuumAtlas.EinsteinMaxwell.NP.npKN_beta_alpha_gamma
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-23T10:21:56.744988+00:00
-- url     : https://prove2.me/theorems/b513cf22-7131-4da9-a7e3-0cff1b66e205
-- title:
--   KN spin coefficients β, α, γ
-- statement:
--   KN spin coefficients β, α, γ
--
--   Closed forms of β, α, γ for the KN Kinnersley frame on domReg (as printed).
--
--   **Scope.** Exactly the hypotheses printed in the formal statement.
--
--   **中文摘要** KN 自旋系数 β、α、γ 闭式。
-- source:
--   He Wang, Exact Spacetime Atlas V: From Linearized Einstein–Maxwell Equations to Kerr–Newman Radiation Systems. Local source, no public repository; commit b8cd107a558e153ed41fb4972ac5315499d14778; Atlas/EinsteinMaxwell/NP/KNWeyl.lean#L105-L120; SHA-256 13cac1a0822e84fed504493d4cce2dee2d08d9f7487c29671f1afdcefef95064. Registered definitions: mission/PHYSICS_BOUNDARY.md (§K–§M); literature: P. Hintz, arXiv:2609.33661 (v1); Mark–Yang–Zimmerman–Chen, arXiv:1409.5800 (v1).

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
import Definitions.Def_Atlas_EinsteinMaxwell_NP_KNComm
import Definitions.Def_Atlas_EinsteinMaxwell_NP_KNFaraday
import Definitions.Def_Atlas_EinsteinMaxwell_NP_KNFrame
import Definitions.Def_Atlas_EinsteinMaxwell_NP_KNSpin
import Definitions.Def_Atlas_EinsteinMaxwell_NP_KNWeyl
import Definitions.Def_Atlas_EinsteinMaxwell_NP_NPScalars
import Definitions.Def_Atlas_EinsteinMaxwell_NP_Riemann
import Definitions.Def_Atlas_Kerr_InAtoms
import Definitions.Def_Atlas_Transport_Connection
import Definitions.Def_Atlas_Transport_MatrixCalc
open Real Complex
open scoped ComplexConjugate
open ExactVacuumAtlas.EinsteinMaxwell.KN (Sig Del gKN giKN faradayKN domReg)
open ExactVacuumAtlas
open ExactVacuumAtlas.EinsteinMaxwell
open ExactVacuumAtlas.EinsteinMaxwell.NP
variable {M a Q : ℝ} {x : Pt 4}
local notation "OM" => omL (gKN M a Q) (giKN M a Q) (knE M a Q) (knTh M a Q)

theorem ExactVacuumAtlas.EinsteinMaxwell.NP.npKN_beta_alpha_gamma (hx : x ∈ domReg M a Q) :
    npBeta (gKN M a Q) (giKN M a Q) (knE M a Q) (knTh M a Q) x
      = ((Real.cos (x 2) / Real.sin (x 2) : ℝ) : ℂ) / (2 * ((Real.sqrt 2 : ℝ) : ℂ) * qK a x) ∧
    npAlpha (gKN M a Q) (giKN M a Q) (knE M a Q) (knTh M a Q) x
      = I * ((a * Real.sin (x 2) : ℝ) : ℂ) / (((Real.sqrt 2 : ℝ) : ℂ) * qbarK a x ^ 2)
        - ((Real.cos (x 2) / Real.sin (x 2) : ℝ) : ℂ) / (2 * ((Real.sqrt 2 : ℝ) : ℂ) * qbarK a x) ∧
    npGamma (gKN M a Q) (giKN M a Q) (knE M a Q) (knTh M a Q) x
      = -((Del M a Q (x 1) : ℝ) : ℂ) / (2 * ((Sig a (x 1) (x 2) : ℝ) : ℂ) * qbarK a x)
        + (((x 1 - M) / (2 * Sig a (x 1) (x 2)) : ℝ) : ℂ) := by sorry
