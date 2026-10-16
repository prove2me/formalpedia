-- Prove2me | Theorems.Thm_ExactVacuumAtlas_Schwarzschild_PG_relation_std_toPG
-- name    : ExactVacuumAtlas.Schwarzschild.PG.relation_std_toPG
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-16T02:31:56.557525+00:00
-- url     : https://prove2.me/theorems/79894c95-718a-4f05-92b0-4883dd0cd593
-- title:
--   Composite standard → PG relation on domStd M
-- statement:
--   Exactly the statement of Release02.pg_std_restricted (composite relation on domStd M = {r > 0, r ≠ 2M, 0 < θ < π}, both sides), of which it is the source.
-- source:
--   He Wang, Exact Vacuum Atlas II, local source snapshot (public Git repository not yet available), commit 11fb317259353b71a41d6daed466c495cffd7db4; Atlas/Schwarzschild/PGStd.lean#L53-L59; SHA-256 088af667b69d8d88eec0c443d81d23005e87d943670ace1c3b33231a0350a279. Mathematical background: See mission/PHYSICS_BOUNDARY.md §A-F for registered definitions and literature references (Wald, Müller-Grave arXiv:0904.4184, Visser arXiv:0706.0622, Martel-Poisson gr-qc/0001069).

import Mathlib
import Definitions.Def_Atlas_Core_Basic
import Definitions.Def_Atlas_Core_Lift
import Definitions.Def_Atlas_Core_Relation
import Definitions.Def_Atlas_Schwarzschild_Defs
import Definitions.Def_Atlas_Schwarzschild_Domain
import Definitions.Def_Atlas_Schwarzschild_EFRelation
import Definitions.Def_Atlas_Schwarzschild_PGDefs
import Definitions.Def_Atlas_Schwarzschild_PGRelation
open Real
open scoped ContDiff
open ExactVacuumAtlas ExactVacuumAtlas.Schwarzschild
open ExactVacuumAtlas
open ExactVacuumAtlas.Schwarzschild
open ExactVacuumAtlas.Schwarzschild.PG
set_option maxHeartbeats 4000000
variable (M ε : ℝ)

theorem ExactVacuumAtlas.Schwarzschild.PG.relation_std_toPG (hM : 0 ≤ M) (hε : ε ^ 2 = 1) :
    CoordRelation (gStd M) (gPG M ε) (domStd M) (domStd M)
      (fun x => pgFromEF M ε (toEF M ε x)) (fun z => fromEF M ε (pgToEF M ε z))
      (fun x => jacInv M ε (toEF M ε x) * EFRelation.jac M ε x) := by sorry
