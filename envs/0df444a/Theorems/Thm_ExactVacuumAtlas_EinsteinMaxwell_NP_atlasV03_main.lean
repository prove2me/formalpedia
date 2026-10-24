-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_NP_atlasV03_main
-- name    : ExactVacuumAtlas.EinsteinMaxwell.NP.atlasV03_main
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-23T10:26:53.902354+00:00
-- url     : https://prove2.me/theorems/ddba015c-e3b1-44ec-b1d7-adf4ba2e8670
-- title:
--   Atlas V main theorem: III's systems (1) and (7) from the complexified linearised Einstein–Maxwell equations
-- statement:
--   Atlas V main theorem: III's systems (1) and (7) from the complexified linearised Einstein–Maxwell equations
--
--   Let p : Hintz2026.SubextremalKN and let τ : CTan be a complex first-order tangent, i.e. a pair of real tangents (h_R, f_R, B_R), (h_I, f_I, B_I) of the metric, the Faraday field and the null frame; let ω, m ∈ ℝ, F : PosFields and G : NegFields. Assume (i) KNCTan p.M p.a p.Q domKN τ: both real parts are compatible real frame tangents at the Kerr–Newman background on the open set domKN ⊆ domReg (C^∞ f and B, antisymmetric f, real pattern of B: the l, n components real and m̄ = conj m, first-order Gram relation); (ii) CLinEM: IV's linearised residuals linEinstein, linMaxwell, linFaraday of the complexified tangent vanish on domKN (equivalently: for both real parts); (iii) the complex phantom gauge cPhi0 τ y = 0 and cPhi2 τ y = 0 for all y ∈ domKN; (iv) PosMode p τ ω m F and NegMode p τ ω m G. Then for every z ∈ U p: Sys1PosAt p ω m F z ∧ Sys7At p 1 ω m (yPos p 1 F) (yPos p (−1) F) z, and Sys1NegAt p ω m G z ∧ Sys7At p (−1) ω m (yNeg p 1 G) (yNeg p (−1) G) z. Sys1PosAt / Sys1NegAt are III's frozen four-equation systems res1a–res1d / res1aN–res1dN; Sys7At is III's system (7). This is a forward source derivation under the chosen gauge and single-mode conditions: linearised Einstein–Maxwell ⇒ III's system (1) ⇒ (via III) system (7). It is not a two-way reconstruction of the full linearised Einstein–Maxwell system from the radiation systems; III's (1) ⇔ (7) does not make the new arrow invertible.
--
--   **Scope.** p : Hintz2026.SubextremalKN — III's parameter structure: M > 0, Q ≠ 0, a² + Q² < M² (a = 0 allowed; Q = 0, the extremal and super-extremal cases are excluded). U p = {(r, θ) : r > r₊, 0 < θ < π} with r₊ = M + √(M² − a² − Q²); domKN p.M p.a p.Q = {x ∈ ℝ⁴ : (x¹, x²) ∈ U p} (t and φ arbitrary real numbers; no horizon, axis or chart gluing). Phantom gauge: cPhi0 τ = 0 (positive branch) and cPhi2 τ = 0 (negative branch) on domKN are conditions on the COMPLEX combinations δΦ₀^ℂ = δΦ₀(τ_R) + i δΦ₀(τ_I), δΦ₂^ℂ; they are not imposed on the two real tangents separately and they are not δF = 0 or δΦ₁ = 0. No gauge reachability is claimed. Single-mode conditions are hypotheses: PosMode / NegMode state that each scaled radiative variable equals phaseP ω m · (amplitude ∘ toRT) on domKN, phaseP ω m x = exp(−iωt + imφ), with real ω and m (0 allowed; m is not required to be an integer; no Fourier completeness, no spectrum). The amplitude regularity PosSmooth / NegSmooth is DERIVED (PosMode.smooth / NegMode.smooth) from the C^∞ tangent and the mode equations.
--
--   **中文摘要** 在亚极端 Kerr–Newman 外域（M>0、Q≠0、a²+Q²<M²，a=0 允许）上：若复切向满足 KNCTan（两份实切向的光滑性、反对称、标架实性与一阶 Gram 关系）、IV 线性化 Einstein–Maxwell 方程的复化 CLinEM、复 phantom 规范 δΦ₀^ℂ=δΦ₂^ℂ=0 以及正负单模式条件，则 III 冻结的正、负系统 (1) 在 U p 上成立，并由 III 的 main_pos_on_U / main_neg_on_U 得到系统 (7)。这是已选规范与单模式条件下的正向来源推导，不是完整 EM 与辐射系统的双向重建。
-- source:
--   He Wang, Exact Spacetime Atlas V: From Linearized Einstein–Maxwell Equations to Kerr–Newman Radiation Systems. Local source, no public repository; commit b8cd107a558e153ed41fb4972ac5315499d14778; Atlas/EinsteinMaxwell/NP/V03Main.lean#L65-L76; SHA-256 a50f3383ee003da70bf318271215f1450b0e38b327c8eb49d74737aa3825bce4. Registered definitions: mission/PHYSICS_BOUNDARY.md (§K–§M); literature: P. Hintz, arXiv:2609.33661 (v1); Mark–Yang–Zimmerman–Chen, arXiv:1409.5800 (v1).

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

theorem ExactVacuumAtlas.EinsteinMaxwell.NP.atlasV03_main (hτ : KNCTan p.M p.a p.Q (domKN p.M p.a p.Q) τ)
    (hL : CLinEM p.M p.a p.Q (domKN p.M p.a p.Q) τ)
    (hg0 : ∀ y ∈ domKN p.M p.a p.Q, cPhi0 p.M p.a p.Q τ y = 0)
    (hg2 : ∀ y ∈ domKN p.M p.a p.Q, cPhi2 p.M p.a p.Q τ y = 0)
    {F : Hintz2026.PosFields} {G : Hintz2026.NegFields} (hF : PosMode p τ om mm F) (hG : NegMode p τ om mm G) :
    (∀ z ∈ Hintz2026.U p, Hintz2026.Sys1PosAt p om mm F z ∧
        Hintz2026.Sys7At p 1 om mm (Hintz2026.yPos p 1 F) (Hintz2026.yPos p (-1) F) z) ∧
      (∀ z ∈ Hintz2026.U p, Hintz2026.Sys1NegAt p om mm G z ∧
        Hintz2026.Sys7At p (-1) om mm (Hintz2026.yNeg p 1 G) (Hintz2026.yNeg p (-1) G) z) := by sorry
