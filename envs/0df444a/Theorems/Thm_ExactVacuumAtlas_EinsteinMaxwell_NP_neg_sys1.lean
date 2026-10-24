-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_NP_neg_sys1
-- name    : ExactVacuumAtlas.EinsteinMaxwell.NP.neg_sys1
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-23T10:25:35.555797+00:00
-- url     : https://prove2.me/theorems/6445f3ae-6ce5-4c6d-bfbd-8284a240ce7d
-- title:
--   Negative branch: III's system (1) from the linearised Einstein–Maxwell equations
-- statement:
--   Negative branch: III's system (1) from the linearised Einstein–Maxwell equations
--
--   For p : SubextremalKN, τ with KNCTan and CLinEM on domKN, the negative gauge cPhi2 τ = 0 on domKN and NegMode p τ ω m G: for every z ∈ U p, Sys1NegAt p ω m G z (III's res1aN, res1bN, res1cN, res1dN vanish). Only the negative-branch gauge is assumed.
--
--   **Scope.** p : Hintz2026.SubextremalKN — III's parameter structure: M > 0, Q ≠ 0, a² + Q² < M² (a = 0 allowed; Q = 0, the extremal and super-extremal cases are excluded). U p = {(r, θ) : r > r₊, 0 < θ < π} with r₊ = M + √(M² − a² − Q²); domKN p.M p.a p.Q = {x ∈ ℝ⁴ : (x¹, x²) ∈ U p} (t and φ arbitrary real numbers; no horizon, axis or chart gluing). Phantom gauge: cPhi0 τ = 0 (positive branch) and cPhi2 τ = 0 (negative branch) on domKN are conditions on the COMPLEX combinations δΦ₀^ℂ = δΦ₀(τ_R) + i δΦ₀(τ_I), δΦ₂^ℂ; they are not imposed on the two real tangents separately and they are not δF = 0 or δΦ₁ = 0. No gauge reachability is claimed.
--
--   **中文摘要** 负支：在 KNCTan、CLinEM、仅负支复规范 δΦ₂^ℂ=0 与负支单模式条件下，III 的 res1aN–res1dN 在 U p 上为零。
-- source:
--   He Wang, Exact Spacetime Atlas V: From Linearized Einstein–Maxwell Equations to Kerr–Newman Radiation Systems. Local source, no public repository; commit b8cd107a558e153ed41fb4972ac5315499d14778; Atlas/EinsteinMaxwell/NP/V03Main.lean#L41-L49; SHA-256 a50f3383ee003da70bf318271215f1450b0e38b327c8eb49d74737aa3825bce4. Registered definitions: mission/PHYSICS_BOUNDARY.md (§K–§M); literature: P. Hintz, arXiv:2609.33661 (v1); Mark–Yang–Zimmerman–Chen, arXiv:1409.5800 (v1).

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
open ExactVacuumAtlas
open ExactVacuumAtlas.EinsteinMaxwell
open ExactVacuumAtlas.EinsteinMaxwell.NP
variable (p : Hintz2026.SubextremalKN) {τ : CTan} {om mm : ℝ}

theorem ExactVacuumAtlas.EinsteinMaxwell.NP.neg_sys1 (hτ : KNCTan p.M p.a p.Q (domKN p.M p.a p.Q) τ) (hL : CLinEM p.M p.a p.Q (domKN p.M p.a p.Q) τ)
    (hg : ∀ y ∈ domKN p.M p.a p.Q, cPhi2 p.M p.a p.Q τ y = 0) {G : Hintz2026.NegFields}
    (hm : NegMode p τ om mm G) : ∀ z ∈ Hintz2026.U p, Hintz2026.Sys1NegAt p om mm G z := by sorry
