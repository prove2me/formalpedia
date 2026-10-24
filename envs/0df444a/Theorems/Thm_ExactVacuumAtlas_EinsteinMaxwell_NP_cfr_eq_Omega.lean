-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_NP_cfr_eq_Omega
-- name    : ExactVacuumAtlas.EinsteinMaxwell.NP.cfr_eq_Omega
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-23T10:21:47.372901+00:00
-- url     : https://prove2.me/theorems/7eb306aa-672e-487f-9b74-425e5ad200c1
-- title:
--   Torsion-freeness in the frame
-- statement:
--   Torsion-freeness in the frame
--
--   c^C_{AB} = Ω_A^C_B − Ω_B^C_A (symmetry of the Christoffel symbols).
--
--   **Scope.** Exactly the hypotheses printed in the formal statement.
--
--   **中文摘要** 无挠：c = Ω_A − Ω_B。
-- source:
--   He Wang, Exact Spacetime Atlas V: From Linearized Einstein–Maxwell Equations to Kerr–Newman Radiation Systems. Local source, no public repository; commit b8cd107a558e153ed41fb4972ac5315499d14778; Atlas/EinsteinMaxwell/NP/FrameConn.lean#L237-L250; SHA-256 2a10cd770a38610029f7546d603b6e7d5f8af619e7c052fbab673dadeffc4f32. Registered definitions: mission/PHYSICS_BOUNDARY.md (§K–§M); literature: P. Hintz, arXiv:2609.33661 (v1); Mark–Yang–Zimmerman–Chen, arXiv:1409.5800 (v1).

import Mathlib
import Definitions.Def_Atlas_Core_Basic
import Definitions.Def_Atlas_EinsteinMaxwell_Basic
import Definitions.Def_Atlas_EinsteinMaxwell_Certificate
import Definitions.Def_Atlas_EinsteinMaxwell_NP_Basic
import Definitions.Def_Atlas_EinsteinMaxwell_NP_CCalc
import Definitions.Def_Atlas_EinsteinMaxwell_NP_FrameConn
import Definitions.Def_Atlas_EinsteinMaxwell_NP_Riemann
import Definitions.Def_Atlas_Transport_Connection
import Definitions.Def_Atlas_Transport_MatrixCalc
open scoped ContDiff Matrix
open Complex
open ExactVacuumAtlas
open ExactVacuumAtlas.EinsteinMaxwell
open ExactVacuumAtlas.EinsteinMaxwell.NP
variable {n : ℕ}

theorem ExactVacuumAtlas.EinsteinMaxwell.NP.cfr_eq_Omega {g gi : Metric n} {E Θ : Fin n → Fin n → Pt n → ℂ} {U : Set (Pt n)}
    (hF : FrameData g gi E Θ U) {x : Pt n} (hx : x ∈ U) (C A B : Fin n) :
    cfr E Θ C A B x = Omega g gi E Θ A x C B - Omega g gi E Θ B x C A := by sorry
