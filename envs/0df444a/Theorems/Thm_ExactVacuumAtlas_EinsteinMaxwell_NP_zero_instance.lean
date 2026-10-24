-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_NP_zero_instance
-- name    : ExactVacuumAtlas.EinsteinMaxwell.NP.zero_instance
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-23T10:27:01.504127+00:00
-- url     : https://prove2.me/theorems/7aeb35f0-da9b-43aa-8701-b4b0b64b0ad0
-- title:
--   The hypothesis bundle of the main theorem is non-empty (zero tangent)
-- statement:
--   The hypothesis bundle of the main theorem is non-empty (zero tangent)
--
--   For every p : SubextremalKN and real ω, m: the zero complex tangent CTan.zero satisfies KNCTan, CLinEM, both phantom gauges, and PosMode / NegMode with zero amplitudes. This only shows the hypotheses are consistent; it does not construct a nonzero radiation mode and does not replace the general theorems.
--
--   **Scope.** p : Hintz2026.SubextremalKN — III's parameter structure: M > 0, Q ≠ 0, a² + Q² < M² (a = 0 allowed; Q = 0, the extremal and super-extremal cases are excluded). U p = {(r, θ) : r > r₊, 0 < θ < π} with r₊ = M + √(M² − a² − Q²); domKN p.M p.a p.Q = {x ∈ ℝ⁴ : (x¹, x²) ∈ U p} (t and φ arbitrary real numbers; no horizon, axis or chart gluing).
--
--   **中文摘要** 零切向与零振幅满足主定理全部前提：仅说明前提束非空，不是非零辐射模式的存在性。
-- source:
--   He Wang, Exact Spacetime Atlas V: From Linearized Einstein–Maxwell Equations to Kerr–Newman Radiation Systems. Local source, no public repository; commit b8cd107a558e153ed41fb4972ac5315499d14778; Atlas/EinsteinMaxwell/NP/V03Main.lean#L129-L174; SHA-256 a50f3383ee003da70bf318271215f1450b0e38b327c8eb49d74737aa3825bce4. Registered definitions: mission/PHYSICS_BOUNDARY.md (§K–§M); literature: P. Hintz, arXiv:2609.33661 (v1); Mark–Yang–Zimmerman–Chen, arXiv:1409.5800 (v1).

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
import Definitions.Def_Atlas_EinsteinMaxwell_NP_V03C3
import Definitions.Def_Atlas_EinsteinMaxwell_NP_V03Cplx
import Definitions.Def_Atlas_EinsteinMaxwell_NP_V03Family
import Definitions.Def_Atlas_EinsteinMaxwell_NP_V03LinKN
import Definitions.Def_Atlas_EinsteinMaxwell_NP_V03LinMx
import Definitions.Def_Atlas_EinsteinMaxwell_NP_V03Main
import Definitions.Def_Atlas_EinsteinMaxwell_NP_V03Mode
import Definitions.Def_Atlas_EinsteinMaxwell_NP_V03Realize
import Definitions.Def_Atlas_EinsteinMaxwell_NP_V03Res
import Definitions.Def_Atlas_EinsteinMaxwell_NP_V03Src
import Definitions.Def_Atlas_EinsteinMaxwell_NP_V03Tan
import Definitions.Def_Atlas_EinsteinMaxwell_NP_V03Var
import Definitions.Def_Atlas_EinsteinMaxwell_Variation_Defs
import Definitions.Def_Atlas_EinsteinMaxwell_Variation_Local
import Definitions.Def_Atlas_Kerr_InAtoms
import Definitions.Def_Atlas_Transport_Connection
import Definitions.Def_Atlas_Transport_MatrixCalc
import Definitions.Def_Hintz2026_Chiral
import Definitions.Def_Hintz2026_Core
import Definitions.Def_Hintz2026_Domain
import Definitions.Def_Hintz2026_System1
import Definitions.Def_Hintz2026_System4
open Complex Filter Topology
open scoped ComplexConjugate Matrix ContDiff
open ExactVacuumAtlas.EinsteinMaxwell ExactVacuumAtlas.Variation
open ExactVacuumAtlas.EinsteinMaxwell.KN (Sig Del gKN giKN domReg domKN faradayKN)

theorem ExactVacuumAtlas.EinsteinMaxwell.NP.zero_instance (p : Hintz2026.SubextremalKN) (om mm : ℝ) :
    KNCTan p.M p.a p.Q (domKN p.M p.a p.Q) CTan.zero ∧ CLinEM p.M p.a p.Q (domKN p.M p.a p.Q) CTan.zero ∧
      (∀ y ∈ domKN p.M p.a p.Q, cPhi0 p.M p.a p.Q CTan.zero y = 0) ∧
      (∀ y ∈ domKN p.M p.a p.Q, cPhi2 p.M p.a p.Q CTan.zero y = 0) ∧
      PosMode p CTan.zero om mm ⟨0, 0, 0, 0⟩ ∧ NegMode p CTan.zero om mm ⟨0, 0, 0, 0⟩ := by sorry
