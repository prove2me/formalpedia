-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_NP_cL_KN_23
-- name    : ExactVacuumAtlas.EinsteinMaxwell.NP.cL_KN_23
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-23T10:21:51.148046+00:00
-- url     : https://prove2.me/theorems/540dae0d-6bb4-4a31-bb9c-9a2e78d99b25
-- title:
--   KN commutator coefficients cL(·, 2, 3)
-- statement:
--   KN commutator coefficients cL(·, 2, 3)
--
--   Closed forms of cL (knE) (knTh) C 2 3 for C = 0…3 on domReg (as printed).
--
--   **Scope.** Exactly the hypotheses printed in the formal statement.
--
--   **中文摘要** KN 对易系数 cL 闭式。
-- source:
--   He Wang, Exact Spacetime Atlas V: From Linearized Einstein–Maxwell Equations to Kerr–Newman Radiation Systems. Local source, no public repository; commit b8cd107a558e153ed41fb4972ac5315499d14778; Atlas/EinsteinMaxwell/NP/KNComm.lean#L447-L467; SHA-256 bc2e5a3ee1709b32fe1e8fb95d154f3b7f3f2e4d32ee7305fe1e8d05012f1b43. Registered definitions: mission/PHYSICS_BOUNDARY.md (§K–§M); literature: P. Hintz, arXiv:2609.33661 (v1); Mark–Yang–Zimmerman–Chen, arXiv:1409.5800 (v1).

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

theorem ExactVacuumAtlas.EinsteinMaxwell.NP.cL_KN_23 (hx : x ∈ domReg M a Q) :
    cL (knE M a Q) (knTh M a Q) 0 2 3 x = -1 / qK a x + 1 / qbarK a x ∧
    cL (knE M a Q) (knTh M a Q) 1 2 3 x = ((Del M a Q (x 1) : ℝ) : ℂ) / (2 * ((Sig a (x 1) (x 2) : ℝ) : ℂ) * qbarK a x)
      - ((Del M a Q (x 1) : ℝ) : ℂ) / (2 * ((Sig a (x 1) (x 2) : ℝ) : ℂ) * qK a x) ∧
    cL (knE M a Q) (knTh M a Q) 2 2 3 x = -(I * ((a * Real.sin (x 2) : ℝ) : ℂ)) / (((Real.sqrt 2 : ℝ) : ℂ) * qK a x ^ 2)
      - ((Real.cos (x 2) / Real.sin (x 2) : ℝ) : ℂ) / (((Real.sqrt 2 : ℝ) : ℂ) * qK a x) ∧
    cL (knE M a Q) (knTh M a Q) 3 2 3 x = ((Real.cos (x 2) / Real.sin (x 2) : ℝ) : ℂ) / (((Real.sqrt 2 : ℝ) : ℂ) * qbarK a x)
      - I * ((a * Real.sin (x 2) : ℝ) : ℂ) / (((Real.sqrt 2 : ℝ) : ℂ) * qbarK a x ^ 2) := by sorry
