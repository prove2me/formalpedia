-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_NP_fdir_Fup
-- name    : ExactVacuumAtlas.EinsteinMaxwell.NP.fdir_Fup
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-23T10:24:12.378992+00:00
-- url     : https://prove2.me/theorems/dad727aa-6b04-4591-8027-1a689eb72c55
-- title:
--   Frame derivative of raised frame components
-- statement:
--   Frame derivative of raised frame components
--
--   D_D (F^{PR}) = Σ_{ST} η^{PS} η^{RT} D_D F_{ST} for C^∞ F.
--
--   **Scope.** Exactly the hypotheses printed in the formal statement.
--
--   **中文摘要** 升指标标架分量的标架导数。
-- source:
--   He Wang, Exact Spacetime Atlas V: From Linearized Einstein–Maxwell Equations to Kerr–Newman Radiation Systems. Local source, no public repository; commit b8cd107a558e153ed41fb4972ac5315499d14778; Atlas/EinsteinMaxwell/NP/NPMaxwell.lean#L259-L273; SHA-256 8db724b88398b27f6bd9e66bffe3dd4d56351f4e6b454026a2dd888370ee2a5e. Registered definitions: mission/PHYSICS_BOUNDARY.md (§K–§M); literature: P. Hintz, arXiv:2609.33661 (v1); Mark–Yang–Zimmerman–Chen, arXiv:1409.5800 (v1).

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
import Definitions.Def_Atlas_EinsteinMaxwell_NP_KNFrame
import Definitions.Def_Atlas_EinsteinMaxwell_NP_NPMaxwell
import Definitions.Def_Atlas_EinsteinMaxwell_NP_NPRicci
import Definitions.Def_Atlas_EinsteinMaxwell_NP_NPScalars
import Definitions.Def_Atlas_EinsteinMaxwell_NP_Riemann
import Definitions.Def_Atlas_Kerr_InAtoms
import Definitions.Def_Atlas_Transport_Connection
import Definitions.Def_Atlas_Transport_MatrixCalc
open scoped ContDiff Matrix
open Complex
open ExactVacuumAtlas
open ExactVacuumAtlas.EinsteinMaxwell
open ExactVacuumAtlas.EinsteinMaxwell.NP
variable {g gi : Metric 4} {E Θ : Fin 4 → Fin 4 → Pt 4 → ℂ} {U : Set (Pt 4)}
variable {F : TwoForm 4}

theorem ExactVacuumAtlas.EinsteinMaxwell.NP.fdir_Fup (hF : FrameData g gi E Θ U) (hFs : ∀ i j, ContDiffOn ℝ ∞ (F i j) U) {x : Pt 4} (hx : x ∈ U)
    (D P R : Fin 4) :
    fdir E D (Fup F E P R) x = ∑ S, ∑ T, etaNull P S * etaNull R T * fdir E D (FfrF F E S T) x := by sorry
