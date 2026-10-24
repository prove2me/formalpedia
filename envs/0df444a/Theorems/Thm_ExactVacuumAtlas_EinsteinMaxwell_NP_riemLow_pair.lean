-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_NP_riemLow_pair
-- name    : ExactVacuumAtlas.EinsteinMaxwell.NP.riemLow_pair
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-23T10:21:49.437453+00:00
-- url     : https://prove2.me/theorems/70f51b11-c6ca-4b15-8a9b-e4e58ca394a7
-- title:
--   Pair symmetry of the Riemann tensor
-- statement:
--   Pair symmetry of the Riemann tensor
--
--   On MetricData sets: R_{cdab} = R_{abcd}.
--
--   **Scope.** Exactly the hypotheses printed in the formal statement.
--
--   **中文摘要** Riemann 对称性 R_{cdab}=R_{abcd}。
-- source:
--   He Wang, Exact Spacetime Atlas V: From Linearized Einstein–Maxwell Equations to Kerr–Newman Radiation Systems. Local source, no public repository; commit b8cd107a558e153ed41fb4972ac5315499d14778; Atlas/EinsteinMaxwell/NP/Riemann.lean#L259-L274; SHA-256 dfe20b65e1328fa8bd4849f7fe94465fa58439b24537be187d13ea5b0e6928df. Registered definitions: mission/PHYSICS_BOUNDARY.md (§K–§M); literature: P. Hintz, arXiv:2609.33661 (v1); Mark–Yang–Zimmerman–Chen, arXiv:1409.5800 (v1).

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

theorem ExactVacuumAtlas.EinsteinMaxwell.NP.riemLow_pair (hm : MetricData g gi U) {y : Pt n} (hy : y ∈ U) (a b c d : Fin n) :
    riemLow g gi c d a b y = riemLow g gi a b c d y := by sorry
