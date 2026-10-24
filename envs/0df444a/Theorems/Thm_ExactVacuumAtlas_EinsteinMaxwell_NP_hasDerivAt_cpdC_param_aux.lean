-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_NP_hasDerivAt_cpdC_param_aux
-- name    : ExactVacuumAtlas.EinsteinMaxwell.NP.hasDerivAt_cpdC_param_aux
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-23T10:18:59.248791+00:00
-- url     : https://prove2.me/theorems/9a06aa9c-025a-4353-9f33-222dfaa190cf
-- title:
--   Parameter derivative commutes with a coordinate partial
-- statement:
--   Parameter derivative commutes with a coordinate partial
--
--   If (ε, y) ↦ φ(ε, y) is C^∞ on an open W and ψ(y) is its ε-derivative at ε₀ on the slice, then ε ↦ cpdC i (φ(ε, ·)) x has derivative cpdC i ψ x at ε₀.
--
--   **Scope.** Exactly the hypotheses printed in the formal statement.
--
--   **中文摘要** 参数导数与坐标偏导交换（联合 C^∞）。
-- source:
--   He Wang, Exact Spacetime Atlas V: From Linearized Einstein–Maxwell Equations to Kerr–Newman Radiation Systems. Local source, no public repository; commit b8cd107a558e153ed41fb4972ac5315499d14778; Atlas/EinsteinMaxwell/NP/V03Joint.lean#L83-L129; SHA-256 9464f44ddafc9a1d1a85a42c012db1d6667cf2a8c76b4b99a4a754b380af6ae3. Registered definitions: mission/PHYSICS_BOUNDARY.md (§K–§M); literature: P. Hintz, arXiv:2609.33661 (v1); Mark–Yang–Zimmerman–Chen, arXiv:1409.5800 (v1).

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

theorem ExactVacuumAtlas.EinsteinMaxwell.NP.hasDerivAt_cpdC_param_aux {φ : ℝ × Pt n → ℂ} {W : Set (ℝ × Pt n)} (hW : IsOpen W)
    (hφ : ContDiffOn ℝ ∞ φ W) {ε₀ : ℝ} {x : Pt n} (hx : (ε₀, x) ∈ W)
    {ψ : Pt n → ℂ} (hψ : ∀ y, (ε₀, y) ∈ W → HasDerivAt (fun ε => φ (ε, y)) (ψ y) ε₀) (i : Fin n) :
    HasDerivAt (fun ε => cpdC i (fun z => φ (ε, z)) x) (cpdC i ψ x) ε₀ := by sorry
