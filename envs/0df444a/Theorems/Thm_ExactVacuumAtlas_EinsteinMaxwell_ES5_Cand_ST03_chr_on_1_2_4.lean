-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_ES5_Cand_ST03_chr_on_1_2_4
-- name    : ExactVacuumAtlas.EinsteinMaxwell.ES5.Cand.ST03.chr_on_1_2_4
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-28T14:12:02.821525+00:00
-- url     : https://prove2.me/theorems/64733525-4c73-408f-89f9-2f884ff6156c
-- title:
--   ST03 (μ = 2, Q = 1, β = 1/3): Christoffel table entry Γ^{1}_{24}
-- statement:
--   ST03 (μ = 2, Q = 1, β = 1/3): Christoffel table entry Γ^{1}_{24}
--
--   Generated table lemma for candidate ST03 (μ = 2, Q = 1, β = 1/3): christoffel gN giN 1 2 4 equals an explicit function of (r, u) (liftRU) on dom (Set.EqOn); gN, giN are the normalised closed forms bound to candG, candGi by bind_g/bind_gi.
--
--   **Scope.** Exactly the hypotheses printed in the formal statement.
--
--   **中文摘要** 候选的 Christoffel 表项（dom 上 EqOn）。
-- source:
--   He Wang, Exact Spacetime Atlas VI: Five-Dimensional Einstein–Maxwell Certificates and Equal-Spin Radial Reduction. Local source, no public repository; commit 4a4048a; Atlas/EinsteinMaxwell/ES5/Cand/ST03/Chr.lean#L565-L570; SHA-256 8889db18705ed72c6ae6c0d74ac13a16045d5413d767d6b1650fd563c7ee8640. Registered definitions: mission/PHYSICS_BOUNDARY.md (§N–§O); literature: R. C. Myers, M. J. Perry, Ann. Phys. 172 (1986) 304; F. R. Tangherlini, Nuovo Cimento 27 (1963) 636.

import Mathlib
import Definitions.Def_Atlas_Core_Basic
import Definitions.Def_Atlas_Core_Certificate
import Definitions.Def_Atlas_EinsteinMaxwell_Basic
import Definitions.Def_Atlas_EinsteinMaxwell_D_Basic
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_Cand_ST03_Defs
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_Defs
open scoped ContDiff
open ExactVacuumAtlas ExactVacuumAtlas.EinsteinMaxwell ExactVacuumAtlas.EinsteinMaxwell.D
open ExactVacuumAtlas.EinsteinMaxwell.ES5
open ExactVacuumAtlas
open ExactVacuumAtlas.EinsteinMaxwell
open ExactVacuumAtlas.EinsteinMaxwell.ES5
open ExactVacuumAtlas.EinsteinMaxwell.ES5.Cand
open ExactVacuumAtlas.EinsteinMaxwell.ES5.Cand.ST03
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

theorem ExactVacuumAtlas.EinsteinMaxwell.ES5.Cand.ST03.chr_on_1_2_4 :
    Set.EqOn (christoffel gN giN 1 2 4) (liftRU (fun r u => (0:ℝ) : ℝ → ℝ → ℝ)) dom := by sorry
