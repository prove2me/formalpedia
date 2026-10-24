-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_NP_KNFam_ricFVar_02
-- name    : ExactVacuumAtlas.EinsteinMaxwell.NP.KNFam.ricFVar_02
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-23T10:19:52.668437+00:00
-- url     : https://prove2.me/theorems/58aaa819-1350-471e-88ef-c8eb2c79786d
-- title:
--   Ricci source through IV's residual: δR(l,m) = L_E(l,m) + (2Q/q²) δΦ₀
-- statement:
--   Ricci source through IV's residual: δR(l,m) = L_E(l,m) + (2Q/q²) δΦ₀
--
--   For a KNFam (Kerr–Newman background at ε = 0) with NPTangent (h, f, B) and (0, x) ∈ W: the genuine first variation ricFVar 0 2 of the frame Ricci component R(l,m) equals LEfr 0 2 — the frame projection L_E(l,m) of IV's linearised Einstein residual — plus 2(Q/q²) phi0Var, with phi0Var the variation of Φ₀ = F(l,m). The coefficient uses q (not q̄).
--
--   **Scope.** Every real M, a, Q; slice points of a KNFam (⊆ domReg).
--
--   **中文摘要** 在 KN 背景族上，R(l,m) 的真实一阶变分 = IV 的 L_E 的 (l,m) 标架投影 + (2Q/q²)δΦ₀。
-- source:
--   He Wang, Exact Spacetime Atlas V: From Linearized Einstein–Maxwell Equations to Kerr–Newman Radiation Systems. Local source, no public repository; commit b8cd107a558e153ed41fb4972ac5315499d14778; Atlas/EinsteinMaxwell/NP/V03Src.lean#L139-L150; SHA-256 cf20b5e9593790bd47fc233d856a0cde0f481acea030139ae7534ec0078491f0. Registered definitions: mission/PHYSICS_BOUNDARY.md (§K–§M); literature: P. Hintz, arXiv:2609.33661 (v1); Mark–Yang–Zimmerman–Chen, arXiv:1409.5800 (v1).

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

theorem ExactVacuumAtlas.EinsteinMaxwell.NP.KNFam.ricFVar_02 (hK : KNFam M a Q g gi F E Θ W) (ht : NPTangent g F E W h f B)
    (hx0 : ((0 : ℝ), x) ∈ W) :
    ricFVar gK giK h EK B 0 2 x = LEfr M a Q h f 0 2 x + 2 * ((Q : ℂ) / qK a x ^ 2) * phi0Var FK f EK B x := by sorry
