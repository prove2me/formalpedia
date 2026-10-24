-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_NP_NullFrameData_cL_eq_ccontr
-- name    : ExactVacuumAtlas.EinsteinMaxwell.NP.NullFrameData.cL_eq_ccontr
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-23T10:19:00.139778+00:00
-- url     : https://prove2.me/theorems/57987dc3-95da-41b2-b20d-82cb876fb412
-- title:
--   Commutator coefficients as contractions
-- statement:
--   Commutator coefficients as contractions
--
--   For a null frame: cL C A B = g(e_C, [e_A, e_B]) as a bilinear contraction.
--
--   **Scope.** Exactly the hypotheses printed in the formal statement.
--
--   **中文摘要** cL 为 g(e_C,[e_A,e_B])。
-- source:
--   He Wang, Exact Spacetime Atlas V: From Linearized Einstein–Maxwell Equations to Kerr–Newman Radiation Systems. Local source, no public repository; commit b8cd107a558e153ed41fb4972ac5315499d14778; Atlas/EinsteinMaxwell/NP/FrameNull.lean#L190-L198; SHA-256 89b93964d08a58f81f17ec29d939043c67b8a5c7a9a375bb5c15b99bf70dff0a. Registered definitions: mission/PHYSICS_BOUNDARY.md (§K–§M); literature: P. Hintz, arXiv:2609.33661 (v1); Mark–Yang–Zimmerman–Chen, arXiv:1409.5800 (v1).

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
import Definitions.Def_Atlas_EinsteinMaxwell_NP_Riemann
import Definitions.Def_Atlas_Kerr_InAtoms
import Definitions.Def_Atlas_Transport_Connection
import Definitions.Def_Atlas_Transport_MatrixCalc
open scoped ContDiff Matrix
open Complex
open ExactVacuumAtlas
open ExactVacuumAtlas.EinsteinMaxwell
open ExactVacuumAtlas.EinsteinMaxwell.NP
open ExactVacuumAtlas.EinsteinMaxwell.NP.NullFrameData
variable {g gi : Metric 4} {E Θ : Fin 4 → Fin 4 → Pt 4 → ℂ} {U : Set (Pt 4)}

theorem ExactVacuumAtlas.EinsteinMaxwell.NP.NullFrameData.cL_eq_ccontr (hN : NullFrameData g gi E Θ U) {x : Pt 4} (hx : x ∈ U) (C A B : Fin 4) :
    cL E Θ C A B x = ccontr g x (fvec E C x) (fun μ => brk E A B μ x) := by sorry
