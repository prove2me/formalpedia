-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_NP_riemFL_formula
-- name    : ExactVacuumAtlas.EinsteinMaxwell.NP.riemFL_formula
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-23T10:21:59.302046+00:00
-- url     : https://prove2.me/theorems/b77fa585-c819-4ae0-8b1d-8a8cae653960
-- title:
--   Lowered frame curvature formula
-- statement:
--   Lowered frame curvature formula
--
--   General null frame: R_{IJAB} = D_A ω_{IBJ} − D_B ω_{IAJ} + Σ_L(ω_{IAL}Ω_B^L_J − ω_{IBL}Ω_A^L_J) − Σ_C c^C_{AB} ω_{ICJ}.
--
--   **Scope.** Exactly the hypotheses printed in the formal statement.
--
--   **中文摘要** 下指标标架曲率公式。
-- source:
--   He Wang, Exact Spacetime Atlas V: From Linearized Einstein–Maxwell Equations to Kerr–Newman Radiation Systems. Local source, no public repository; commit b8cd107a558e153ed41fb4972ac5315499d14778; Atlas/EinsteinMaxwell/NP/NPScalars.lean#L69-L91; SHA-256 0407b4962e3abe6546c882ba615247c64310e983f6809bae77f3724bf2e0f285. Registered definitions: mission/PHYSICS_BOUNDARY.md (§K–§M); literature: P. Hintz, arXiv:2609.33661 (v1); Mark–Yang–Zimmerman–Chen, arXiv:1409.5800 (v1).

import Mathlib
import Definitions.Def_Atlas_Core_Basic
import Definitions.Def_Atlas_Core_Lift
import Definitions.Def_Atlas_EinsteinMaxwell_Basic
import Definitions.Def_Atlas_EinsteinMaxwell_Certificate
import Definitions.Def_Atlas_EinsteinMaxwell_KN_Defs
import Definitions.Def_Atlas_EinsteinMaxwell_KN_Domain
import Definitions.Def_Atlas_EinsteinMaxwell_NP_Basic
import Definitions.Def_Atlas_EinsteinMaxwell_NP_CCalc
import Definitions.Def_Atlas_EinsteinMaxwell_NP_FrameConn
import Definitions.Def_Atlas_EinsteinMaxwell_NP_FrameNull
import Definitions.Def_Atlas_EinsteinMaxwell_NP_KNFrame
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

theorem ExactVacuumAtlas.EinsteinMaxwell.NP.riemFL_formula (hN : NullFrameData g gi E Θ U) {x : Pt 4} (hx : x ∈ U) (I J A B : Fin 4) :
    riemFL g gi E Θ I J A B x = fdir E A (omL g gi E Θ I B J) x - fdir E B (omL g gi E Θ I A J) x
      + ∑ L, (omL g gi E Θ I A L x * Omega g gi E Θ B x L J - omL g gi E Θ I B L x * Omega g gi E Θ A x L J)
      - ∑ C, cfr E Θ C A B x * omL g gi E Θ I C J x := by sorry
