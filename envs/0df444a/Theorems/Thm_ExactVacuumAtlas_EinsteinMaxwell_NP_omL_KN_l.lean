-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_NP_omL_KN_l
-- name    : ExactVacuumAtlas.EinsteinMaxwell.NP.omL_KN_l
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-23T10:21:55.064994+00:00
-- url     : https://prove2.me/theorems/dc7dd699-99b7-4d86-a05e-2e53e517e3c5
-- title:
--   KN connection components in direction e_0
-- statement:
--   KN connection components in direction e_0
--
--   Closed forms of omL C 0 B for the KN frame on domReg.
--
--   **Scope.** Exactly the hypotheses printed in the formal statement.
--
--   **中文摘要** KN 标架联络分量闭式。
-- source:
--   He Wang, Exact Spacetime Atlas V: From Linearized Einstein–Maxwell Equations to Kerr–Newman Radiation Systems. Local source, no public repository; commit b8cd107a558e153ed41fb4972ac5315499d14778; Atlas/EinsteinMaxwell/NP/KNOmega.lean#L118-L128; SHA-256 c951e138ba281fe843b19757b5ea10c8d02f75cbe3345e789fa129d678bad2ab. Registered definitions: mission/PHYSICS_BOUNDARY.md (§K–§M); literature: P. Hintz, arXiv:2609.33661 (v1); Mark–Yang–Zimmerman–Chen, arXiv:1409.5800 (v1).

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

theorem ExactVacuumAtlas.EinsteinMaxwell.NP.omL_KN_l (hx : x ∈ domReg M a Q) :
    omL (gKN M a Q) (KN.giKN M a Q) (knE M a Q) (knTh M a Q) 0 0 1 x = 0 ∧
    omL (gKN M a Q) (KN.giKN M a Q) (knE M a Q) (knTh M a Q) 0 0 2 x = 0 ∧
    omL (gKN M a Q) (KN.giKN M a Q) (knE M a Q) (knTh M a Q) 0 0 3 x = 0 ∧
    omL (gKN M a Q) (KN.giKN M a Q) (knE M a Q) (knTh M a Q) 1 0 2 x
      = I * ((a * Real.sin (x 2) : ℝ) : ℂ) / (((Real.sqrt 2 : ℝ) : ℂ) * qK a x ^ 2) ∧
    omL (gKN M a Q) (KN.giKN M a Q) (knE M a Q) (knTh M a Q) 1 0 3 x
      = -(I * ((a * Real.sin (x 2) : ℝ) : ℂ)) / (((Real.sqrt 2 : ℝ) : ℂ) * qbarK a x ^ 2) ∧
    omL (gKN M a Q) (KN.giKN M a Q) (knE M a Q) (knTh M a Q) 2 0 3 x = 0 := by sorry
