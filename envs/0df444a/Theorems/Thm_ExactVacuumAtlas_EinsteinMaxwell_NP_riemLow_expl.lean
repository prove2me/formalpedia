-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_NP_riemLow_expl
-- name    : ExactVacuumAtlas.EinsteinMaxwell.NP.riemLow_expl
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-23T10:21:45.218978+00:00
-- url     : https://prove2.me/theorems/92be745c-803e-457d-87ad-d6907b24c267
-- title:
--   Explicit lowered Riemann tensor
-- statement:
--   Explicit lowered Riemann tensor
--
--   R_{abcd} = ½(∂_c∂_b g_{ad} − ∂_c∂_a g_{db} − ∂_d∂_b g_{ac} + ∂_d∂_a g_{cb}) + Σ g^{ef}(Γ_{e,da}Γ_{f,cb} − Γ_{e,ca}Γ_{f,db}).
--
--   **Scope.** Exactly the hypotheses printed in the formal statement.
--
--   **中文摘要** 下指标 Riemann 的显式公式。
-- source:
--   He Wang, Exact Spacetime Atlas V: From Linearized Einstein–Maxwell Equations to Kerr–Newman Radiation Systems. Local source, no public repository; commit b8cd107a558e153ed41fb4972ac5315499d14778; Atlas/EinsteinMaxwell/NP/Riemann.lean#L219-L235; SHA-256 dfe20b65e1328fa8bd4849f7fe94465fa58439b24537be187d13ea5b0e6928df. Registered definitions: mission/PHYSICS_BOUNDARY.md (§K–§M); literature: P. Hintz, arXiv:2609.33661 (v1); Mark–Yang–Zimmerman–Chen, arXiv:1409.5800 (v1).

import Mathlib
import Definitions.Def_Atlas_Core_Basic
import Definitions.Def_Atlas_EinsteinMaxwell_Basic
import Definitions.Def_Atlas_EinsteinMaxwell_Certificate
import Definitions.Def_Atlas_EinsteinMaxwell_NP_Riemann
import Definitions.Def_Atlas_Transport_Connection
import Definitions.Def_Atlas_Transport_MatrixCalc
open scoped ContDiff
open Matrix
open ExactVacuumAtlas
open ExactVacuumAtlas.EinsteinMaxwell
open ExactVacuumAtlas.EinsteinMaxwell.NP
variable {n : ℕ}
variable {g gi : Metric n} {U : Set (Pt n)}

theorem ExactVacuumAtlas.EinsteinMaxwell.NP.riemLow_expl (hm : MetricData g gi U) {y : Pt n} (hy : y ∈ U) (a b c d : Fin n) :
    riemLow g gi a b c d y = (hessG g c b a d y - hessG g c a d b y - hessG g d b a c y
      + hessG g d a c b y) / 2 + quadQ g gi a b c d y := by sorry
