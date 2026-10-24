-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_NP_ricciOf_eq_riemLow_contr
-- name    : ExactVacuumAtlas.EinsteinMaxwell.NP.ricciOf_eq_riemLow_contr
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-23T10:18:58.641408+00:00
-- url     : https://prove2.me/theorems/6bf56e1d-ab29-4c4d-a54c-e9cbde77f795
-- title:
--   Ricci as a contraction of the lowered Riemann tensor
-- statement:
--   Ricci as a contraction of the lowered Riemann tensor
--
--   R_{bd} = Σ_{ac} g^{ac} R_{abcd} (registered ricciOf).
--
--   **Scope.** Exactly the hypotheses printed in the formal statement.
--
--   **中文摘要** Ricci 为下指标 Riemann 的缩并。
-- source:
--   He Wang, Exact Spacetime Atlas V: From Linearized Einstein–Maxwell Equations to Kerr–Newman Radiation Systems. Local source, no public repository; commit b8cd107a558e153ed41fb4972ac5315499d14778; Atlas/EinsteinMaxwell/NP/Riemann.lean#L303-L316; SHA-256 dfe20b65e1328fa8bd4849f7fe94465fa58439b24537be187d13ea5b0e6928df. Registered definitions: mission/PHYSICS_BOUNDARY.md (§K–§M); literature: P. Hintz, arXiv:2609.33661 (v1); Mark–Yang–Zimmerman–Chen, arXiv:1409.5800 (v1).

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

theorem ExactVacuumAtlas.EinsteinMaxwell.NP.ricciOf_eq_riemLow_contr (hm : MetricData g gi U) {y : Pt n} (hy : y ∈ U) (b d : Fin n) :
    ricciOf g gi b d y = ∑ a, ∑ c, gi a c y * riemLow g gi a b c d y := by sorry
