-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_NP_knRealize
-- name    : ExactVacuumAtlas.EinsteinMaxwell.NP.knRealize
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-23T10:23:13.144772+00:00
-- url     : https://prove2.me/theorems/e9d9143b-c2a9-43a2-9eff-6f073e94fc20
-- title:
--   Realisation: every compatible real frame tangent at Kerr–Newman is the tangent of a kinematic family
-- statement:
--   Realisation: every compatible real frame tangent at Kerr–Newman is the tangent of a kinematic family
--
--   For every real M, a, Q, every open U ⊆ domReg M a Q and every RealFrameTangent (gKN) (knE) U h f B (C^∞ f and B, antisymmetric f, real pattern of B, first-order Gram relation) there are families g, gi, F, E, Θ on an open W ⊆ ℝ × ℝ⁴ with KNFam M a Q g gi F E Θ W (Kerr–Newman background at ε = 0), NPTangent g F E W h f B (the tangent is exactly (h, f, B)) and {y : (0, y) ∈ W} = U. The family is kinematic only: it is NOT required to solve the Einstein–Maxwell equations for ε ≠ 0.
--
--   **Scope.** Every real M, a, Q; open U ⊆ domReg.
--
--   **中文摘要** 对 KN 背景上任意相容实标架切向，存在以其为切向的运动学族（ε=0 为 KN，切片恰为 U）；族本身不要求满足场方程。
-- source:
--   He Wang, Exact Spacetime Atlas V: From Linearized Einstein–Maxwell Equations to Kerr–Newman Radiation Systems. Local source, no public repository; commit b8cd107a558e153ed41fb4972ac5315499d14778; Atlas/EinsteinMaxwell/NP/V03Tan.lean#L149-L160; SHA-256 88d223b286fff847db42a44c2b8c71064c081113221bdb31e78120407fc8aaad. Registered definitions: mission/PHYSICS_BOUNDARY.md (§K–§M); literature: P. Hintz, arXiv:2609.33661 (v1); Mark–Yang–Zimmerman–Chen, arXiv:1409.5800 (v1).

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
import Definitions.Def_Atlas_EinsteinMaxwell_NP_KNComm
import Definitions.Def_Atlas_EinsteinMaxwell_NP_KNFaraday
import Definitions.Def_Atlas_EinsteinMaxwell_NP_KNFrame
import Definitions.Def_Atlas_EinsteinMaxwell_NP_KNSpin
import Definitions.Def_Atlas_EinsteinMaxwell_NP_KNWeyl
import Definitions.Def_Atlas_EinsteinMaxwell_NP_ModeOperators
import Definitions.Def_Atlas_EinsteinMaxwell_NP_NPBianchi
import Definitions.Def_Atlas_EinsteinMaxwell_NP_NPMaxwell
import Definitions.Def_Atlas_EinsteinMaxwell_NP_NPRicci
import Definitions.Def_Atlas_EinsteinMaxwell_NP_NPScalars
import Definitions.Def_Atlas_EinsteinMaxwell_NP_Riemann
import Definitions.Def_Atlas_EinsteinMaxwell_NP_V03Cplx
import Definitions.Def_Atlas_EinsteinMaxwell_NP_V03Family
import Definitions.Def_Atlas_EinsteinMaxwell_NP_V03LinKN
import Definitions.Def_Atlas_EinsteinMaxwell_NP_V03LinMx
import Definitions.Def_Atlas_EinsteinMaxwell_NP_V03Realize
import Definitions.Def_Atlas_EinsteinMaxwell_NP_V03Src
import Definitions.Def_Atlas_EinsteinMaxwell_NP_V03Tan
import Definitions.Def_Atlas_EinsteinMaxwell_NP_V03Var
import Definitions.Def_Atlas_EinsteinMaxwell_Variation_Defs
import Definitions.Def_Atlas_EinsteinMaxwell_Variation_Local
import Definitions.Def_Atlas_Kerr_InAtoms
import Definitions.Def_Atlas_Transport_Connection
import Definitions.Def_Atlas_Transport_MatrixCalc
import Definitions.Def_Hintz2026_Core
import Definitions.Def_Hintz2026_Domain
import Definitions.Def_Hintz2026_System1
import Definitions.Def_Hintz2026_System4
open Complex Filter Topology
open scoped ComplexConjugate Matrix ContDiff
open ExactVacuumAtlas.EinsteinMaxwell ExactVacuumAtlas.Variation
open ExactVacuumAtlas.EinsteinMaxwell.KN (Sig Del gKN giKN domReg domKN faradayKN)
open ExactVacuumAtlas
open ExactVacuumAtlas.EinsteinMaxwell
open ExactVacuumAtlas.EinsteinMaxwell.NP
variable {M a Q : ℝ}

theorem ExactVacuumAtlas.EinsteinMaxwell.NP.knRealize {U : Set (Pt 4)} (hU : IsOpen U) (hUD : U ⊆ domReg M a Q) {h : Metric 4} {f : TwoForm 4}
    {B : Fin 4 → Fin 4 → Pt 4 → ℂ} (ht : RealFrameTangent (gKN M a Q) (knE M a Q) U h f B) :
    ∃ (g gi : ℝ → Metric 4) (F : ℝ → TwoForm 4) (E Θ : ℝ → Fin 4 → Fin 4 → Pt 4 → ℂ) (W : Set (ℝ × Pt 4)),
      KNFam M a Q g gi F E Θ W ∧ NPTangent g F E W h f B ∧ {y | ((0 : ℝ), y) ∈ W} = U := by sorry
