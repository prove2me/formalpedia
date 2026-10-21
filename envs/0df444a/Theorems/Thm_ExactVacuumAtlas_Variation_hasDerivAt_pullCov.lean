-- Prove2me | Theorems.Thm_ExactVacuumAtlas_Variation_hasDerivAt_pullCov
-- name    : ExactVacuumAtlas.Variation.hasDerivAt_pullCov
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-21T01:51:59.567156+00:00
-- url     : https://prove2.me/theorems/4175b22a-0a17-4e5b-8c4b-66941b9caae0
-- title:
--   Derivative of the pull-back is the Lie derivative
-- statement:
--   Derivative of the pull-back is the Lie derivative
--
--   For C^∞ T on open U and y ∈ U: HasDerivAt (ε ↦ pullCov ξ T ε a b y) ((lieCov2 ξ T) a b y) 0.
--
--   **Scope.** Exactly the hypotheses printed in the formal statement.
--
--   **中文摘要** 拉回的参数导数等于 Lie 导数。
-- source:
--   He Wang, Exact Spacetime Atlas IV: Certified Einstein–Maxwell Backgrounds and First Variations. Local source, no public repository; commit 543904bfcfa3bb169f43fc4d9dbd569999b71886; Atlas/EinsteinMaxwell/Variation/Gauge.lean#L171-L189; SHA-256 46d8b5f079abb433286efd867efe3e39da3c640c54b8be946e36e83eaf1a0127. Registered definitions and literature: mission/PHYSICS_BOUNDARY.md (§H–§J); Müller–Grave arXiv:0904.4184; Newman et al., J. Math. Phys. 6 (1965) 918.

import Mathlib
import Definitions.Def_Atlas_Core_Basic
import Definitions.Def_Atlas_Core_Certificate
import Definitions.Def_Atlas_EinsteinMaxwell_Basic
import Definitions.Def_Atlas_EinsteinMaxwell_Certificate
import Definitions.Def_Atlas_EinsteinMaxwell_Variation_Defs
import Definitions.Def_Atlas_EinsteinMaxwell_Variation_Gauge
import Definitions.Def_Atlas_EinsteinMaxwell_Variation_Local
import Definitions.Def_Atlas_Transport_Connection
import Definitions.Def_Atlas_Transport_MatrixCalc
open Filter Topology
open scoped ContDiff
open Matrix
open ExactVacuumAtlas.EinsteinMaxwell
open ExactVacuumAtlas
open ExactVacuumAtlas.Variation
variable {n : ℕ}

theorem ExactVacuumAtlas.Variation.hasDerivAt_pullCov {U : Set (Pt n)} (hU : IsOpen U) {T : Fin n → Fin n → Pt n → ℝ}
    (hT : ∀ i j, ContDiffOn ℝ ∞ (T i j) U) (ξ : Fin n → Pt n → ℝ) {y : Pt n} (hy : y ∈ U) (a b : Fin n) :
    HasDerivAt (fun ε => pullCov ξ T ε a b y) (lieCov2 ξ T a b y) 0 := by sorry
