-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_ES5_Cand_NW01_ric_1_1
-- name    : ExactVacuumAtlas.EinsteinMaxwell.ES5.Cand.NW01.ric_1_1
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-28T14:08:56.875982+00:00
-- url     : https://prove2.me/theorems/3d240e48-deee-4b9e-9550-db6126228ba1
-- title:
--   NW01 (MP01 data with wrong W): Ricci table entry R_{11}
-- statement:
--   NW01 (MP01 data with wrong W): Ricci table entry R_{11}
--
--   Generated table lemma for candidate NW01 (MP01 data with wrong W): ricciOf gN giN 1 1 x equals the closed form printed in the statement for every x ∈ dom.
--
--   **Scope.** Exactly the hypotheses printed in the formal statement.
--
--   **中文摘要** 候选的 Ricci 表项（dom 上）。
-- source:
--   He Wang, Exact Spacetime Atlas VI: Five-Dimensional Einstein–Maxwell Certificates and Equal-Spin Radial Reduction. Local source, no public repository; commit 4a4048a; Atlas/EinsteinMaxwell/ES5/Cand/NW01/Ricci.lean#L18-L22; SHA-256 09047a74b1c6ac7929d932621287904eec15ec5201493a98c88c5814bd7076f9. Registered definitions: mission/PHYSICS_BOUNDARY.md (§N–§O); literature: R. C. Myers, M. J. Perry, Ann. Phys. 172 (1986) 304; F. R. Tangherlini, Nuovo Cimento 27 (1963) 636.

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

theorem ExactVacuumAtlas.EinsteinMaxwell.ES5.Cand.NW01.ric_1_1 (x : Pt 5) (hx : x ∈ dom) :
    ricciOf gN giN 1 1 x = ((3623878656:ℝ) * x 1 ^ 14 + (5435817984:ℝ) * x 1 ^ 12 + (7474249728:ℝ) * x 1 ^ 10 + (5209325568:ℝ) * x 1 ^ 8 + (3779592192:ℝ) * x 1 ^ 6 + (1295253504:ℝ) * x 1 ^ 4 + (526417920:ℝ) * x 1 ^ 2) / ((1:ℝ) * fDl (x 1) * fP (x 1) ^ 2 * fS (x 1) ^ 7) := by sorry
