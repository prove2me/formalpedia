-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_NP_psi2_KN
-- name    : ExactVacuumAtlas.EinsteinMaxwell.NP.psi2_KN
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-23T10:21:52.61381+00:00
-- url     : https://prove2.me/theorems/b7d7485e-22e1-4043-af54-6128d49fbd5f
-- title:
--   Kerr–Newman background Weyl scalar Ψ₂ = (Q² − Mq)/(q q̄³)
-- statement:
--   Kerr–Newman background Weyl scalar Ψ₂ = (Q² − Mq)/(q q̄³)
--
--   For every real M, a, Q and x ∈ domReg: the background NP scalar psi2 (gKN) (giKN) (knE) at x equals (Q² − M q)/(q q̄³), q = r + i a cos θ. This is the BACKGROUND Ψ₂ (Hintz convention, g_H = −g), not III's radiative unknown ψ₂.
--
--   **Scope.** Every real M, a, Q; points of domReg.
--
--   **中文摘要** KN 背景 Weyl 标量 Ψ₂=(Q²−Mq)/(q q̄³)（背景量，不是 III 的辐射未知量 ψ₂）。
-- source:
--   He Wang, Exact Spacetime Atlas V: From Linearized Einstein–Maxwell Equations to Kerr–Newman Radiation Systems. Local source, no public repository; commit b8cd107a558e153ed41fb4972ac5315499d14778; Atlas/EinsteinMaxwell/NP/KNWeyl.lean#L397-L402; SHA-256 13cac1a0822e84fed504493d4cce2dee2d08d9f7487c29671f1afdcefef95064. Registered definitions: mission/PHYSICS_BOUNDARY.md (§K–§M); literature: P. Hintz, arXiv:2609.33661 (v1); Mark–Yang–Zimmerman–Chen, arXiv:1409.5800 (v1).

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

theorem ExactVacuumAtlas.EinsteinMaxwell.NP.psi2_KN (hx : x ∈ domReg M a Q) :
    psi2 (gKN M a Q) (giKN M a Q) (knE M a Q) x = ((Q : ℂ) ^ 2 - (M : ℂ) * qK a x) / (qK a x * qbarK a x ^ 3) := by sorry
