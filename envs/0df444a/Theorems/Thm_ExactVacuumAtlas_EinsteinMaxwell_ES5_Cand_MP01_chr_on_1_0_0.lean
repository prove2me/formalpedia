-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_ES5_Cand_MP01_chr_on_1_0_0
-- name    : ExactVacuumAtlas.EinsteinMaxwell.ES5.Cand.MP01.chr_on_1_0_0
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-28T13:50:59.676148+00:00
-- url     : https://prove2.me/theorems/6acb6a5a-9cf5-40de-b64e-9363d34e18eb
-- title:
--   MP01 (μ = 3, a = 1/2): Christoffel table entry Γ^{1}_{00}
-- statement:
--   MP01 (μ = 3, a = 1/2): Christoffel table entry Γ^{1}_{00}
--
--   Generated table lemma for candidate MP01 (μ = 3, a = 1/2): christoffel gN giN 1 0 0 equals an explicit function of (r, u) (liftRU) on dom (Set.EqOn); gN, giN are the normalised closed forms bound to candG, candGi by bind_g/bind_gi.
--
--   **Scope.** Exactly the hypotheses printed in the formal statement.
--
--   **中文摘要** 候选的 Christoffel 表项（dom 上 EqOn）。
-- source:
--   He Wang, Exact Spacetime Atlas VI: Five-Dimensional Einstein–Maxwell Certificates and Equal-Spin Radial Reduction. Local source, no public repository; commit 4a4048a; Atlas/EinsteinMaxwell/ES5/Cand/MP01/Chr.lean#L490-L495; SHA-256 579852ad501dc5fb127d39ea1568832e6df93c261cf0e4bd33e2fe75f3430707. Registered definitions: mission/PHYSICS_BOUNDARY.md (§N–§O); literature: R. C. Myers, M. J. Perry, Ann. Phys. 172 (1986) 304; F. R. Tangherlini, Nuovo Cimento 27 (1963) 636.

import Mathlib
import Definitions.Def_Atlas_Core_Basic
import Definitions.Def_Atlas_Core_Certificate
import Definitions.Def_Atlas_EinsteinMaxwell_Basic
import Definitions.Def_Atlas_EinsteinMaxwell_D_Basic
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_Cand_MP01_Defs
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_Defs
open scoped ContDiff
open ExactVacuumAtlas ExactVacuumAtlas.EinsteinMaxwell ExactVacuumAtlas.EinsteinMaxwell.D
open ExactVacuumAtlas.EinsteinMaxwell.ES5
open ExactVacuumAtlas
open ExactVacuumAtlas.EinsteinMaxwell
open ExactVacuumAtlas.EinsteinMaxwell.ES5
open ExactVacuumAtlas.EinsteinMaxwell.ES5.Cand
open ExactVacuumAtlas.EinsteinMaxwell.ES5.Cand.MP01
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

theorem ExactVacuumAtlas.EinsteinMaxwell.ES5.Cand.MP01.chr_on_1_0_0 :
    Set.EqOn (christoffel gN giN 1 0 0) (liftRU (fun r u => ((192:ℝ) * r ^ 4 + (-480:ℝ) * r ^ 2 + (12:ℝ)) / ((1:ℝ) * fS r ^ 3 * r) : ℝ → ℝ → ℝ)) dom := by sorry
