-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_ES5_einsteinMaxwellD_congr_of_eqOn
-- name    : ExactVacuumAtlas.EinsteinMaxwell.ES5.einsteinMaxwellD_congr_of_eqOn
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-28T13:54:08.70127+00:00
-- url     : https://prove2.me/theorems/3a5e7696-98f0-4429-99d0-27fb0999a0e2
-- title:
--   Einstein–Maxwell residual depends only on data on an open set
-- statement:
--   Einstein–Maxwell residual depends only on data on an open set
--
--   Componentwise EqOn of g, ginv, F on an open U gives equal einsteinMaxwellD at every x ∈ U (statement as printed).
--
--   **Scope.** Exactly the hypotheses printed in the formal statement.
--
--   **中文摘要** 开集上数据相同则 Einstein–Maxwell 残差相同。
-- source:
--   He Wang, Exact Spacetime Atlas VI: Five-Dimensional Einstein–Maxwell Certificates and Equal-Spin Radial Reduction. Local source, no public repository; commit 4a4048a; Atlas/EinsteinMaxwell/ES5/Tools.lean#L69-L78; SHA-256 8eb33cdee8c5956f9a82565c80aa58b049e59e7e5ed43a4f1176098b09966a0a. Registered definitions: mission/PHYSICS_BOUNDARY.md (§N–§O); literature: R. C. Myers, M. J. Perry, Ann. Phys. 172 (1986) 304; F. R. Tangherlini, Nuovo Cimento 27 (1963) 636.

import Mathlib
import Definitions.Def_Atlas_Core_Basic
import Definitions.Def_Atlas_Core_Certificate
import Definitions.Def_Atlas_EinsteinMaxwell_Basic
import Definitions.Def_Atlas_EinsteinMaxwell_D_Basic
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_Defs
open scoped ContDiff
open ExactVacuumAtlas ExactVacuumAtlas.EinsteinMaxwell ExactVacuumAtlas.EinsteinMaxwell.D
open ExactVacuumAtlas
open ExactVacuumAtlas.EinsteinMaxwell
open ExactVacuumAtlas.EinsteinMaxwell.ES5
variable {U : Set (Pt 5)} {f : Pt 5 → ℝ} {F : ℝ → ℝ → ℝ} {x : Pt 5}
variable {g g' ginv ginv' : Metric 5} {Fm Fm' : TwoForm 5}

theorem ExactVacuumAtlas.EinsteinMaxwell.ES5.einsteinMaxwellD_congr_of_eqOn (hU : IsOpen U) (hg : ∀ i j, Set.EqOn (g i j) (g' i j) U)
    (hgi : ∀ i j, Set.EqOn (ginv i j) (ginv' i j) U) (hF : ∀ i j, Set.EqOn (Fm i j) (Fm' i j) U)
    (hx : x ∈ U) (a b : Fin 5) :
    einsteinMaxwellD g ginv Fm a b x = einsteinMaxwellD g' ginv' Fm' a b x := by sorry
