-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_ES5_Generic_chr_on_3_4_4
-- name    : ExactVacuumAtlas.EinsteinMaxwell.ES5.Generic.chr_on_3_4_4
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-28T14:02:24.858319+00:00
-- url     : https://prove2.me/theorems/cb7e4edc-2815-44fb-9c8b-d85698a0046c
-- title:
--   Generic Christoffel table entry Γ^{3}_{44}
-- statement:
--   Generic Christoffel table entry Γ^{3}_{44}
--
--   Under ESData R B D A H W Φ Ψ: christoffel (gG …) (giG …) 3 4 4 equals an explicit expression in the radial functions and their derivatives on esDomain R (Set.EqOn).
--
--   **Scope.** Exactly the hypotheses printed in the formal statement.
--
--   **中文摘要** 一般拟设的 Christoffel 表项（ESData 下）。
-- source:
--   He Wang, Exact Spacetime Atlas VI: Five-Dimensional Einstein–Maxwell Certificates and Equal-Spin Radial Reduction. Local source, no public repository; commit 4a4048a; Atlas/EinsteinMaxwell/ES5/Generic/Chr.lean#L494-L499; SHA-256 7969b90c2a7848fc5435190d3843e621e1b6ba48aee3acc4f2df0ac792d996ba. Registered definitions: mission/PHYSICS_BOUNDARY.md (§N–§O); literature: R. C. Myers, M. J. Perry, Ann. Phys. 172 (1986) 304; F. R. Tangherlini, Nuovo Cimento 27 (1963) 636.

import Mathlib
import Definitions.Def_Atlas_Core_Basic
import Definitions.Def_Atlas_Core_Certificate
import Definitions.Def_Atlas_EinsteinMaxwell_Basic
import Definitions.Def_Atlas_EinsteinMaxwell_D_Basic
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_Defs
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_Generic_Data
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_Generic_Tables
open scoped ContDiff
open ExactVacuumAtlas ExactVacuumAtlas.EinsteinMaxwell ExactVacuumAtlas.EinsteinMaxwell.D
open ExactVacuumAtlas.EinsteinMaxwell.ES5
open ExactVacuumAtlas
open ExactVacuumAtlas.EinsteinMaxwell
open ExactVacuumAtlas.EinsteinMaxwell.ES5
open ExactVacuumAtlas.EinsteinMaxwell.ES5.Generic
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
variable {R : Set ℝ} {B D A H W Φ Ψ : ℝ → ℝ}

theorem ExactVacuumAtlas.EinsteinMaxwell.ES5.Generic.chr_on_3_4_4 (hE : ESData R B D A H W Φ Ψ) :
    Set.EqOn (christoffel (gG B D A H W) (giG B D A H W) 3 4 4) (liftRU (fun r u => (0:ℝ) : ℝ → ℝ → ℝ)) (esDomain R) := by sorry
