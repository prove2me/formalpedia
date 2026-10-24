-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_NP_hasDerivAt_fdir_param_of_zero
-- name    : ExactVacuumAtlas.EinsteinMaxwell.NP.hasDerivAt_fdir_param_of_zero
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-23T10:19:00.333389+00:00
-- url     : https://prove2.me/theorems/f11fa0ba-3ccb-4eaf-a07b-eaebbc38e81b
-- title:
--   First variation of a frame derivative, vanishing background
-- statement:
--   First variation of a frame derivative, vanishing background
--
--   Variant of hasDerivAt_fdir_param: if Φ₀ vanishes on an open neighbourhood of x, the frame-variation term drops out (∂_μ Φ₀(x) = 0 is proved, not assumed).
--
--   **Scope.** Exactly the hypotheses printed in the formal statement.
--
--   **中文摘要** 背景在开邻域为零时标架变分项消失（已证明）。
-- source:
--   He Wang, Exact Spacetime Atlas V: From Linearized Einstein–Maxwell Equations to Kerr–Newman Radiation Systems. Local source, no public repository; commit b8cd107a558e153ed41fb4972ac5315499d14778; Atlas/EinsteinMaxwell/NP/V03Joint.lean#L159-L172; SHA-256 9464f44ddafc9a1d1a85a42c012db1d6667cf2a8c76b4b99a4a754b380af6ae3. Registered definitions: mission/PHYSICS_BOUNDARY.md (§K–§M); literature: P. Hintz, arXiv:2609.33661 (v1); Mark–Yang–Zimmerman–Chen, arXiv:1409.5800 (v1).

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
import Definitions.Def_Atlas_EinsteinMaxwell_Variation_Defs
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
open ExactVacuumAtlas
open ExactVacuumAtlas.EinsteinMaxwell
open ExactVacuumAtlas.EinsteinMaxwell.NP
variable {n : ℕ}

theorem ExactVacuumAtlas.EinsteinMaxwell.NP.hasDerivAt_fdir_param_of_zero {E : ℝ → Fin n → Fin n → Pt n → ℂ} {B : Fin n → Fin n → Pt n → ℂ}
    {Φ : ℝ → Pt n → ℂ} {ψ : Pt n → ℂ} {W : Set (ℝ × Pt n)} {A : Fin n} (hW : IsOpen W)
    (hΦ : ContDiffOn ℝ ∞ (fun p : ℝ × Pt n => Φ p.1 p.2) W) {x : Pt n} (hx : ((0 : ℝ), x) ∈ W)
    (hB : ∀ μ, HasDerivAt (fun ε => E ε A μ x) (B A μ x) 0)
    (hψ : ∀ y, ((0 : ℝ), y) ∈ W → HasDerivAt (fun ε => Φ ε y) (ψ y) 0)
    (h0 : ∀ y, ((0 : ℝ), y) ∈ W → Φ 0 y = 0) :
    HasDerivAt (fun ε => fdir (E ε) A (Φ ε) x) (fdir (E 0) A ψ x) 0 := by sorry
