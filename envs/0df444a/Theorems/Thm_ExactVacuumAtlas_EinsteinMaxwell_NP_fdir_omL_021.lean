-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_NP_fdir_omL_021
-- name    : ExactVacuumAtlas.EinsteinMaxwell.NP.fdir_omL_021
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-23T10:22:00.479059+00:00
-- url     : https://prove2.me/theorems/0fd4fc36-76c8-406b-992f-303d2eef74c3
-- title:
--   Frame derivative of the KN connection component omL 0 2 1
-- statement:
--   Frame derivative of the KN connection component omL 0 2 1
--
--   Closed form of a frame derivative of omL 0 2 1 on domReg (as printed).
--
--   **Scope.** Exactly the hypotheses printed in the formal statement.
--
--   **中文摘要** KN 联络分量的标架导数闭式。
-- source:
--   He Wang, Exact Spacetime Atlas V: From Linearized Einstein–Maxwell Equations to Kerr–Newman Radiation Systems. Local source, no public repository; commit b8cd107a558e153ed41fb4972ac5315499d14778; Atlas/EinsteinMaxwell/NP/KNWeyl.lean#L198-L211; SHA-256 13cac1a0822e84fed504493d4cce2dee2d08d9f7487c29671f1afdcefef95064. Registered definitions: mission/PHYSICS_BOUNDARY.md (§K–§M); literature: P. Hintz, arXiv:2609.33661 (v1); Mark–Yang–Zimmerman–Chen, arXiv:1409.5800 (v1).

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

theorem ExactVacuumAtlas.EinsteinMaxwell.NP.fdir_omL_021 (hx : x ∈ domReg M a Q) :
    fdir (knE M a Q) 0 (omL (gKN M a Q) (giKN M a Q) (knE M a Q) (knTh M a Q) 0 2 1) x
      = -(-(I * ((a * Real.sin (x 2) : ℝ) : ℂ)) * (((Real.sqrt 2 : ℝ) : ℂ) * (2 * qK a x)))
        / (((Real.sqrt 2 : ℝ) : ℂ) * qK a x ^ 2) ^ 2 := by sorry
