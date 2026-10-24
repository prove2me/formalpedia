-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_NP_ricF_KN
-- name    : ExactVacuumAtlas.EinsteinMaxwell.NP.ricF_KN
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-23T10:22:06.23716+00:00
-- url     : https://prove2.me/theorems/ad30575b-031d-4b65-b8c8-5ffc72dfb77b
-- title:
--   IV's Ricci tensor in the KN frame
-- statement:
--   IV's Ricci tensor in the KN frame
--
--   On domReg, the only potentially nonzero frame-Ricci entries are R(l,n) = R(n,l) = R(m,m̄) = R(m̄,m) = Q²/Σ²; all remaining entries are zero. The formula also covers Q = 0, in which case these four entries vanish as well.
--
--   **Scope.** Exactly the hypotheses printed in the formal statement.
--
--   **中文摘要** KN 标架 Ricci：仅 (l,n)、(n,l)、(m,m̄)、(m̄,m) 四个位置可能非零，其值均为 Q²/Σ²，其余为零；Q=0 时这四项也为零。
-- source:
--   He Wang, Exact Spacetime Atlas V: From Linearized Einstein–Maxwell Equations to Kerr–Newman Radiation Systems. Local source, no public repository; commit b8cd107a558e153ed41fb4972ac5315499d14778; Atlas/EinsteinMaxwell/NP/KNWeyl.lean#L162-L173; SHA-256 13cac1a0822e84fed504493d4cce2dee2d08d9f7487c29671f1afdcefef95064. Registered definitions: mission/PHYSICS_BOUNDARY.md (§K–§M); literature: P. Hintz, arXiv:2609.33661 (v1); Mark–Yang–Zimmerman–Chen, arXiv:1409.5800 (v1).

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

theorem ExactVacuumAtlas.EinsteinMaxwell.NP.ricF_KN (hx : x ∈ domReg M a Q) (A B : Fin 4) :
    ricF (gKN M a Q) (giKN M a Q) (knE M a Q) A B x
      = (!![0, ((Q ^ 2 / Sig a (x 1) (x 2) ^ 2 : ℝ) : ℂ), 0, 0; ((Q ^ 2 / Sig a (x 1) (x 2) ^ 2 : ℝ) : ℂ), 0, 0, 0;
          0, 0, 0, ((Q ^ 2 / Sig a (x 1) (x 2) ^ 2 : ℝ) : ℂ); 0, 0, ((Q ^ 2 / Sig a (x 1) (x 2) ^ 2 : ℝ) : ℂ), 0] :
          Matrix (Fin 4) (Fin 4) ℂ) A B := by sorry
