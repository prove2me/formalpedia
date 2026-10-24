-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_NP_hasDerivAt_coframe_of
-- name    : ExactVacuumAtlas.EinsteinMaxwell.NP.hasDerivAt_coframe_of
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-23T10:18:57.633465+00:00
-- url     : https://prove2.me/theorems/292854d0-83a6-4c59-9230-adadff0883e8
-- title:
--   Coframe variation δθ = −ΘBΘ
-- statement:
--   Coframe variation δθ = −ΘBΘ
--
--   For a jointly C^∞ coframe family dual to a frame family on W: ε ↦ Θ_ε has derivative coVar (Θ 0) B = −Θ B Θ (derivative of Θ_ε E_ε = 1).
--
--   **Scope.** Exactly the hypotheses printed in the formal statement.
--
--   **中文摘要** 余标架变分 δθ=−ΘBΘ。
-- source:
--   He Wang, Exact Spacetime Atlas V: From Linearized Einstein–Maxwell Equations to Kerr–Newman Radiation Systems. Local source, no public repository; commit b8cd107a558e153ed41fb4972ac5315499d14778; Atlas/EinsteinMaxwell/NP/V03Family.lean#L104-L145; SHA-256 f001c2ffe97be7cb54821fc20999d8e3421a6ca079fc1d83110f9ad9b80590e4. Registered definitions: mission/PHYSICS_BOUNDARY.md (§K–§M); literature: P. Hintz, arXiv:2609.33661 (v1); Mark–Yang–Zimmerman–Chen, arXiv:1409.5800 (v1).

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
import Definitions.Def_Atlas_EinsteinMaxwell_NP_V03Family
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

theorem ExactVacuumAtlas.EinsteinMaxwell.NP.hasDerivAt_coframe_of {E Θ : ℝ → Fin 4 → Fin 4 → Pt 4 → ℂ} {B : Fin 4 → Fin 4 → Pt 4 → ℂ}
    {W : Set (ℝ × Pt 4)} (hW : IsOpen W) (hΘs : ∀ C ν, ContDiffOn ℝ ∞ (fun p : ℝ × Pt 4 => Θ p.1 C ν p.2) W)
    (hdual : ∀ p ∈ W, coMat (Θ p.1) p.2 * frMat (E p.1) p.2 = 1) {x : Pt 4} (hx : ((0 : ℝ), x) ∈ W)
    (hB : ∀ A μ, HasDerivAt (fun ε => E ε A μ x) (B A μ x) 0) (C ν : Fin 4) :
    HasDerivAt (fun ε => Θ ε C ν x) (coVar (Θ 0) B C ν x) 0 := by sorry
