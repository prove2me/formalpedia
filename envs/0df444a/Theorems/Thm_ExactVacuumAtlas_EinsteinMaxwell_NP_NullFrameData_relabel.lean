-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_NP_NullFrameData_relabel
-- name    : ExactVacuumAtlas.EinsteinMaxwell.NP.NullFrameData.relabel
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-23T10:19:17.942126+00:00
-- url     : https://prove2.me/theorems/27a9d4db-49f7-4b96-937a-4f414218e13c
-- title:
--   Relabelled null frame
-- statement:
--   Relabelled null frame
--
--   Relabelling by an involutive index permutation that preserves etaNull keeps a null frame a null frame.
--
--   **Scope.** Exactly the hypotheses printed in the formal statement.
--
--   **中文摘要** 保持 etaNull 的对合重标仍为零标架。
-- source:
--   He Wang, Exact Spacetime Atlas V: From Linearized Einstein–Maxwell Equations to Kerr–Newman Radiation Systems. Local source, no public repository; commit b8cd107a558e153ed41fb4972ac5315499d14778; Atlas/EinsteinMaxwell/NP/NPScalars.lean#L227-L246; SHA-256 0407b4962e3abe6546c882ba615247c64310e983f6809bae77f3724bf2e0f285. Registered definitions: mission/PHYSICS_BOUNDARY.md (§K–§M); literature: P. Hintz, arXiv:2609.33661 (v1); Mark–Yang–Zimmerman–Chen, arXiv:1409.5800 (v1).

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
variable {σ : Fin 4 → Fin 4}

theorem ExactVacuumAtlas.EinsteinMaxwell.NP.NullFrameData.relabel (hN : NullFrameData g gi E Θ U) (hσ : ∀ A, σ (σ A) = A)
    (hη : ∀ A B, etaNull (σ A) (σ B) = etaNull A B) :
    NullFrameData g gi (NP.relabel σ E) (NP.relabel σ Θ) U := by sorry
