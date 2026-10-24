-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_NP_NullFrameData_weylF_eq
-- name    : ExactVacuumAtlas.EinsteinMaxwell.NP.NullFrameData.weylF_eq
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-23T10:19:17.756667+00:00
-- url     : https://prove2.me/theorems/e0240fed-b670-4502-bf69-6bc1848e35ca
-- title:
--   Frame Weyl decomposition
-- statement:
--   Frame Weyl decomposition
--
--   For a null frame (no field equation): C_{IJAB} = R_{IJAB} − ½(η_{IA}R_{JB} − η_{IB}R_{JA} − η_{JA}R_{IB} + η_{JB}R_{IA}) + (R/6)(η_{IA}η_{JB} − η_{IB}η_{JA}).
--
--   **Scope.** Exactly the hypotheses printed in the formal statement.
--
--   **中文摘要** 标架 Weyl 分解（无场方程）。
-- source:
--   He Wang, Exact Spacetime Atlas V: From Linearized Einstein–Maxwell Equations to Kerr–Newman Radiation Systems. Local source, no public repository; commit b8cd107a558e153ed41fb4972ac5315499d14778; Atlas/EinsteinMaxwell/NP/FrameNull.lean#L353-L370; SHA-256 89b93964d08a58f81f17ec29d939043c67b8a5c7a9a375bb5c15b99bf70dff0a. Registered definitions: mission/PHYSICS_BOUNDARY.md (§K–§M); literature: P. Hintz, arXiv:2609.33661 (v1); Mark–Yang–Zimmerman–Chen, arXiv:1409.5800 (v1).

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

theorem ExactVacuumAtlas.EinsteinMaxwell.NP.NullFrameData.weylF_eq (hN : NullFrameData g gi E Θ U) {x : Pt 4} (hx : x ∈ U) (I J A B : Fin 4) :
    weylF g gi E I J A B x = riemFL g gi E Θ I J A B x
      - (etaNull I A * ricF g gi E J B x - etaNull I B * ricF g gi E J A x
        - etaNull J A * ricF g gi E I B x + etaNull J B * ricF g gi E I A x) / 2
      + (ricciScalar g gi x : ℂ) * (etaNull I A * etaNull J B - etaNull I B * etaNull J A) / 6 := by sorry
