-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_NP_ricF_eq_stress_KN
-- name    : ExactVacuumAtlas.EinsteinMaxwell.NP.ricF_eq_stress_KN
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-23T10:22:24.015855+00:00
-- url     : https://prove2.me/theorems/20c1d51c-b3a1-47e1-94cf-e8b14cb2a191
-- title:
--   KN frame Ricci from the stress
-- statement:
--   KN frame Ricci from the stress
--
--   On domReg: Ric(e_A, e_B) = 2 S(e_A, e_B) for the KN background (E = 0).
--
--   **Scope.** Exactly the hypotheses printed in the formal statement.
--
--   **中文摘要** KN 背景 Ricci = 2S。
-- source:
--   He Wang, Exact Spacetime Atlas V: From Linearized Einstein–Maxwell Equations to Kerr–Newman Radiation Systems. Local source, no public repository; commit b8cd107a558e153ed41fb4972ac5315499d14778; Atlas/EinsteinMaxwell/NP/KNWeyl.lean#L147-L160; SHA-256 13cac1a0822e84fed504493d4cce2dee2d08d9f7487c29671f1afdcefef95064. Registered definitions: mission/PHYSICS_BOUNDARY.md (§K–§M); literature: P. Hintz, arXiv:2609.33661 (v1); Mark–Yang–Zimmerman–Chen, arXiv:1409.5800 (v1).

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

theorem ExactVacuumAtlas.EinsteinMaxwell.NP.ricF_eq_stress_KN (hx : x ∈ domReg M a Q) (A B : Fin 4) :
    ricF (gKN M a Q) (giKN M a Q) (knE M a Q) A B x
      = 2 * ccontr (emStress (gKN M a Q) (giKN M a Q) (faradayKN a Q)) x (fvec (knE M a Q) A x)
        (fvec (knE M a Q) B x) := by sorry
