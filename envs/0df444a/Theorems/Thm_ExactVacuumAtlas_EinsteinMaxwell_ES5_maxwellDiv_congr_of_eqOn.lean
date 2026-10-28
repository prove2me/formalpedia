-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_ES5_maxwellDiv_congr_of_eqOn
-- name    : ExactVacuumAtlas.EinsteinMaxwell.ES5.maxwellDiv_congr_of_eqOn
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-28T13:54:02.915982+00:00
-- url     : https://prove2.me/theorems/6700610b-f44d-48d6-be1b-76f30b6282e2
-- title:
--   Maxwell divergence depends only on data on an open set
-- statement:
--   Maxwell divergence depends only on data on an open set
--
--   Componentwise EqOn of g, ginv, F on an open U gives equal maxwellDiv at every x ∈ U (statement as printed).
--
--   **Scope.** Exactly the hypotheses printed in the formal statement.
--
--   **中文摘要** 开集上数据相同则 Maxwell 散度相同。
-- source:
--   He Wang, Exact Spacetime Atlas VI: Five-Dimensional Einstein–Maxwell Certificates and Equal-Spin Radial Reduction. Local source, no public repository; commit 4a4048a; Atlas/EinsteinMaxwell/ES5/Tools.lean#L80-L89; SHA-256 8eb33cdee8c5956f9a82565c80aa58b049e59e7e5ed43a4f1176098b09966a0a. Registered definitions: mission/PHYSICS_BOUNDARY.md (§N–§O); literature: R. C. Myers, M. J. Perry, Ann. Phys. 172 (1986) 304; F. R. Tangherlini, Nuovo Cimento 27 (1963) 636.

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

theorem ExactVacuumAtlas.EinsteinMaxwell.ES5.maxwellDiv_congr_of_eqOn (hU : IsOpen U) (hg : ∀ i j, Set.EqOn (g i j) (g' i j) U)
    (hgi : ∀ i j, Set.EqOn (ginv i j) (ginv' i j) U) (hF : ∀ i j, Set.EqOn (Fm i j) (Fm' i j) U)
    (hx : x ∈ U) (b : Fin 5) : maxwellDiv g ginv Fm b x = maxwellDiv g' ginv' Fm' b x := by sorry
