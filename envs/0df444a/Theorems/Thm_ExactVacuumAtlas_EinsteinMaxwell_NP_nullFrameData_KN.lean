-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_NP_nullFrameData_KN
-- name    : ExactVacuumAtlas.EinsteinMaxwell.NP.nullFrameData_KN
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-23T10:19:05.679807+00:00
-- url     : https://prove2.me/theorems/b1c6717f-7e3b-47fd-ad3a-e2ca15ed0863
-- title:
--   The KN Kinnersley frame is a null frame
-- statement:
--   The KN Kinnersley frame is a null frame
--
--   NullFrameData for gKN, giKN, knE, knTh on domReg (every real M, a, Q).
--
--   **Scope.** Exactly the hypotheses printed in the formal statement.
--
--   **中文摘要** KN Kinnersley 标架满足零标架条件。
-- source:
--   He Wang, Exact Spacetime Atlas V: From Linearized Einstein–Maxwell Equations to Kerr–Newman Radiation Systems. Local source, no public repository; commit b8cd107a558e153ed41fb4972ac5315499d14778; Atlas/EinsteinMaxwell/NP/KNSpin.lean#L100-L111; SHA-256 296633d32af53ca44cec2982a7dc3dc99a1cb3e71bd617f51817c313623dfb02. Registered definitions: mission/PHYSICS_BOUNDARY.md (§K–§M); literature: P. Hintz, arXiv:2609.33661 (v1); Mark–Yang–Zimmerman–Chen, arXiv:1409.5800 (v1).

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
import Definitions.Def_Atlas_EinsteinMaxwell_NP_KNFaraday
import Definitions.Def_Atlas_EinsteinMaxwell_NP_KNFrame
import Definitions.Def_Atlas_EinsteinMaxwell_NP_KNSpin
import Definitions.Def_Atlas_EinsteinMaxwell_NP_Riemann
import Definitions.Def_Atlas_Kerr_InAtoms
import Definitions.Def_Atlas_Transport_Connection
import Definitions.Def_Atlas_Transport_MatrixCalc
open Real Complex
open scoped ComplexConjugate Matrix ContDiff
open ExactVacuumAtlas.EinsteinMaxwell.KN (Sig Del gKN giKN faradayKN domReg)

theorem ExactVacuumAtlas.EinsteinMaxwell.NP.nullFrameData_KN (M a Q : ℝ) :
    NullFrameData (gKN M a Q) (giKN M a Q) (knE M a Q) (knTh M a Q) (domReg M a Q) := by sorry
