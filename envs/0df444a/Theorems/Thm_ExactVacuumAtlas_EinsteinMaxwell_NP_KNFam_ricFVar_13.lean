-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_NP_KNFam_ricFVar_13
-- name    : ExactVacuumAtlas.EinsteinMaxwell.NP.KNFam.ricFVar_13
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-23T10:21:16.503589+00:00
-- url     : https://prove2.me/theorems/7eaec6ea-f6c6-44ba-981a-ec898dc785c2
-- title:
--   Ricci source through IV's residual: δR(n,m̄) = L_E(n,m̄) + (2Q/q²) δΦ₂
-- statement:
--   Ricci source through IV's residual: δR(n,m̄) = L_E(n,m̄) + (2Q/q²) δΦ₂
--
--   Negative-branch companion of milestone 8: ricFVar 1 3 = LEfr 1 3 + 2(Q/q²) phi2Var, with phi2Var the variation of Φ₂ = F(m̄, n) (frame indices (3, 1)).
--
--   **Scope.** Every real M, a, Q; slice points of a KNFam.
--
--   **中文摘要** 负支对应：R(n,m̄) 的一阶变分 = L_E(n,m̄) + (2Q/q²)δΦ₂。
-- source:
--   He Wang, Exact Spacetime Atlas V: From Linearized Einstein–Maxwell Equations to Kerr–Newman Radiation Systems. Local source, no public repository; commit b8cd107a558e153ed41fb4972ac5315499d14778; Atlas/EinsteinMaxwell/NP/V03Src.lean#L152-L163; SHA-256 cf20b5e9593790bd47fc233d856a0cde0f481acea030139ae7534ec0078491f0. Registered definitions: mission/PHYSICS_BOUNDARY.md (§K–§M); literature: P. Hintz, arXiv:2609.33661 (v1); Mark–Yang–Zimmerman–Chen, arXiv:1409.5800 (v1).

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
variable {M a Q : ℝ} {x : Pt 4}
local notation "gK" => gKN M a Q
local notation "giK" => giKN M a Q
local notation "EK" => knE M a Q
local notation "ΘK" => knTh M a Q
local notation "FK" => faradayKN a Q
variable {g gi : ℝ → Metric 4} {F : ℝ → TwoForm 4} {E Θ : ℝ → Fin 4 → Fin 4 → Pt 4 → ℂ}
  {W : Set (ℝ × Pt 4)} {h : Metric 4} {f : TwoForm 4} {B : Fin 4 → Fin 4 → Pt 4 → ℂ}

theorem ExactVacuumAtlas.EinsteinMaxwell.NP.KNFam.ricFVar_13 (hK : KNFam M a Q g gi F E Θ W) (ht : NPTangent g F E W h f B)
    (hx0 : ((0 : ℝ), x) ∈ W) :
    ricFVar gK giK h EK B 1 3 x = LEfr M a Q h f 1 3 x + 2 * ((Q : ℂ) / qK a x ^ 2) * phi2Var FK f EK B x := by sorry
