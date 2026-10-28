-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_ES5_Cand_NW01_chr_on_0_0_3
-- name    : ExactVacuumAtlas.EinsteinMaxwell.ES5.Cand.NW01.chr_on_0_0_3
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-28T14:08:34.097863+00:00
-- url     : https://prove2.me/theorems/576d9cdf-2f4e-4de1-9b74-c213a773d10f
-- title:
--   NW01 (MP01 data with wrong W): Christoffel table entry Γ^{0}_{03}
-- statement:
--   NW01 (MP01 data with wrong W): Christoffel table entry Γ^{0}_{03}
--
--   Generated table lemma for candidate NW01 (MP01 data with wrong W): christoffel gN giN 0 0 3 equals an explicit function of (r, u) (liftRU) on dom (Set.EqOn); gN, giN are the normalised closed forms bound to candG, candGi by bind_g/bind_gi.
--
--   **Scope.** Exactly the hypotheses printed in the formal statement.
--
--   **中文摘要** 候选的 Christoffel 表项（dom 上 EqOn）。
-- source:
--   He Wang, Exact Spacetime Atlas VI: Five-Dimensional Einstein–Maxwell Certificates and Equal-Spin Radial Reduction. Local source, no public repository; commit 4a4048a; Atlas/EinsteinMaxwell/ES5/Cand/NW01/Chr.lean#L388-L393; SHA-256 b8257a8bffc011512d2d8a2d47f0f0d26c002129791ae34072efca3417968f56. Registered definitions: mission/PHYSICS_BOUNDARY.md (§N–§O); literature: R. C. Myers, M. J. Perry, Ann. Phys. 172 (1986) 304; F. R. Tangherlini, Nuovo Cimento 27 (1963) 636.

import Mathlib
import Definitions.Def_Atlas_Core_Basic
import Definitions.Def_Atlas_Core_Certificate
import Definitions.Def_Atlas_EinsteinMaxwell_Basic
import Definitions.Def_Atlas_EinsteinMaxwell_D_Basic
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_Cand_NW01_Defs
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_Defs
open scoped ContDiff
open ExactVacuumAtlas ExactVacuumAtlas.EinsteinMaxwell ExactVacuumAtlas.EinsteinMaxwell.D
open ExactVacuumAtlas.EinsteinMaxwell.ES5
open ExactVacuumAtlas
open ExactVacuumAtlas.EinsteinMaxwell
open ExactVacuumAtlas.EinsteinMaxwell.ES5
open ExactVacuumAtlas.EinsteinMaxwell.ES5.Cand
open ExactVacuumAtlas.EinsteinMaxwell.ES5.Cand.NW01
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

theorem ExactVacuumAtlas.EinsteinMaxwell.ES5.Cand.NW01.chr_on_0_0_3 :
    Set.EqOn (christoffel gN giN 0 0 3) (liftRU (fun r u => (0:ℝ) : ℝ → ℝ → ℝ)) dom := by sorry
