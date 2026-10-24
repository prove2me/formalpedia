-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_NP_cL_KN_01
-- name    : ExactVacuumAtlas.EinsteinMaxwell.NP.cL_KN_01
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-23T10:22:24.725845+00:00
-- url     : https://prove2.me/theorems/095c32db-15e2-4cf2-a8ae-93278c07b090
-- title:
--   KN commutator coefficients cL(·, 0, 1)
-- statement:
--   KN commutator coefficients cL(·, 0, 1)
--
--   On domReg, this theorem gives the three displayed closed forms of cL (knE) (knTh) C 0 1 for C = 0, 1, 2. It does not include the C = 3 component in its conclusion.
--
--   **Scope.** Exactly the hypotheses printed in the formal statement.
--
--   **中文摘要** KN 对易系数 cL(C,0,1) 在 domReg 上的三个闭式：C=0、1、2；本条结论不包含 C=3。
-- source:
--   He Wang, Exact Spacetime Atlas V: From Linearized Einstein–Maxwell Equations to Kerr–Newman Radiation Systems. Local source, no public repository; commit b8cd107a558e153ed41fb4972ac5315499d14778; Atlas/EinsteinMaxwell/NP/KNComm.lean#L399-L413; SHA-256 bc2e5a3ee1709b32fe1e8fb95d154f3b7f3f2e4d32ee7305fe1e8d05012f1b43. Registered definitions: mission/PHYSICS_BOUNDARY.md (§K–§M); literature: P. Hintz, arXiv:2609.33661 (v1); Mark–Yang–Zimmerman–Chen, arXiv:1409.5800 (v1).

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
import Definitions.Def_Atlas_EinsteinMaxwell_NP_Riemann
import Definitions.Def_Atlas_Kerr_InAtoms
import Definitions.Def_Atlas_Transport_Connection
import Definitions.Def_Atlas_Transport_MatrixCalc
open Real Complex
open scoped ComplexConjugate
open ExactVacuumAtlas.EinsteinMaxwell.KN (Sig Del gKN domReg)
open ExactVacuumAtlas
open ExactVacuumAtlas.EinsteinMaxwell
open ExactVacuumAtlas.EinsteinMaxwell.NP
variable {M a Q : ℝ} {x : Pt 4}

theorem ExactVacuumAtlas.EinsteinMaxwell.NP.cL_KN_01 (hx : x ∈ domReg M a Q) :
    cL (knE M a Q) (knTh M a Q) 0 0 1 x = 0 ∧
    cL (knE M a Q) (knTh M a Q) 1 0 1 x
      = (((x 1 - M) / Sig a (x 1) (x 2) - Del M a Q (x 1) * x 1 / Sig a (x 1) (x 2) ^ 2 : ℝ) : ℂ) ∧
    cL (knE M a Q) (knTh M a Q) 2 0 1 x = -(I * ((a * Real.sin (x 2) : ℝ) : ℂ)) / (((Real.sqrt 2 : ℝ) : ℂ) * qK a x ^ 2)
      - I * ((a * Real.sin (x 2) : ℝ) : ℂ) / (((Real.sqrt 2 : ℝ) : ℂ) * ((Sig a (x 1) (x 2) : ℝ) : ℂ)) := by sorry
