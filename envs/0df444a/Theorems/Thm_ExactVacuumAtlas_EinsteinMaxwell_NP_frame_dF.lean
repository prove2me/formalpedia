-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_NP_frame_dF
-- name    : ExactVacuumAtlas.EinsteinMaxwell.NP.frame_dF
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-23T10:24:18.420276+00:00
-- url     : https://prove2.me/theorems/16eba46a-13a4-4e0d-acaf-8cd4baa6bbc6
-- title:
--   H = dF in a general frame
-- statement:
--   H = dF in a general frame
--
--   For antisymmetric C^∞ F: the frame components of H = dF expressed by frame derivatives and commutators only.
--
--   **Scope.** Exactly the hypotheses printed in the formal statement.
--
--   **中文摘要** 一般标架下 H=dF。
-- source:
--   He Wang, Exact Spacetime Atlas V: From Linearized Einstein–Maxwell Equations to Kerr–Newman Radiation Systems. Local source, no public repository; commit b8cd107a558e153ed41fb4972ac5315499d14778; Atlas/EinsteinMaxwell/NP/NPMaxwell.lean#L107-L123; SHA-256 8db724b88398b27f6bd9e66bffe3dd4d56351f4e6b454026a2dd888370ee2a5e. Registered definitions: mission/PHYSICS_BOUNDARY.md (§K–§M); literature: P. Hintz, arXiv:2609.33661 (v1); Mark–Yang–Zimmerman–Chen, arXiv:1409.5800 (v1).

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

theorem ExactVacuumAtlas.EinsteinMaxwell.NP.frame_dF (hF : FrameData g gi E Θ U) {F : TwoForm 4} (hFs : ∀ i j, ContDiffOn ℝ ∞ (F i j) U)
    (hFa : ∀ y ∈ U, ∀ i j, F i j y = -F j i y) {x : Pt 4} (hx : x ∈ U) (A B C : Fin 4) :
    Hfr F E A B C x = fdir E A (FfrF F E B C) x + fdir E B (FfrF F E C A) x + fdir E C (FfrF F E A B) x
      - ∑ K, (cfr E Θ K A B x * FfrF F E K C x + cfr E Θ K B C x * FfrF F E K A x
        + cfr E Θ K C A x * FfrF F E K B x) := by sorry
