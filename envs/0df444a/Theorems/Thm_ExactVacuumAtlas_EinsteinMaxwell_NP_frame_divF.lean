-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_NP_frame_divF
-- name    : ExactVacuumAtlas.EinsteinMaxwell.NP.frame_divF
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-23T10:24:06.644653+00:00
-- url     : https://prove2.me/theorems/f046adb2-e12b-4803-950b-a4a3c77811f4
-- title:
--   J = ∇·F in a general null frame
-- statement:
--   J = ∇·F in a general null frame
--
--   The dual-coframe component of J = maxwellDiv in terms of frame derivatives and connection coefficients.
--
--   **Scope.** Exactly the hypotheses printed in the formal statement.
--
--   **中文摘要** 零标架下 J=∇·F。
-- source:
--   He Wang, Exact Spacetime Atlas V: From Linearized Einstein–Maxwell Equations to Kerr–Newman Radiation Systems. Local source, no public repository; commit b8cd107a558e153ed41fb4972ac5315499d14778; Atlas/EinsteinMaxwell/NP/NPMaxwell.lean#L192-L239; SHA-256 8db724b88398b27f6bd9e66bffe3dd4d56351f4e6b454026a2dd888370ee2a5e. Registered definitions: mission/PHYSICS_BOUNDARY.md (§K–§M); literature: P. Hintz, arXiv:2609.33661 (v1); Mark–Yang–Zimmerman–Chen, arXiv:1409.5800 (v1).

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

theorem ExactVacuumAtlas.EinsteinMaxwell.NP.frame_divF (hN : NullFrameData g gi E Θ U) {F : TwoForm 4} (hFs : ∀ i j, ContDiffOn ℝ ∞ (F i j) U)
    {x : Pt 4} (hx : x ∈ U) (B : Fin 4) :
    Jfr g gi F Θ B x = ∑ P, fdir E P (Fup F E P B) x
      + ∑ P, (∑ K, Omega g gi E Θ K x K P) * Fup F E P B x
      + ∑ P, ∑ R, Omega g gi E Θ P x B R * Fup F E P R x := by sorry
