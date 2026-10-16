-- Prove2me | Theorems.Thm_ExactVacuumAtlas_Schwarzschild_PG_hasDerivAt_qf
-- name    : ExactVacuumAtlas.Schwarzschild.PG.hasDerivAt_qf
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-15T22:38:02.725126+00:00
-- url     : https://prove2.me/theorems/09dd6543-9835-4dae-b5bb-9f1a0e9813f4
-- title:
--   Derivative of the PG velocity atom q = √(2M/r)
-- statement:
--   For real M ≥ 0 and r > 0: u ↦ q(M, u) = √(2M/u) has derivative −q(M, r)/(2r) at r (HasDerivAt).
-- source:
--   He Wang, Exact Vacuum Atlas II, local source snapshot (public Git repository not yet available), commit 11fb317259353b71a41d6daed466c495cffd7db4; Atlas/Schwarzschild/PGAtoms.lean#L32-L49; SHA-256 608cd138269990ef8e1653998f4250e275f3957f867d624dbee913f03ed06e21. Mathematical background: See mission/PHYSICS_BOUNDARY.md §A-F for registered definitions and literature references (Wald, Müller-Grave arXiv:0904.4184, Visser arXiv:0706.0622, Martel-Poisson gr-qc/0001069).

import Mathlib
import Definitions.Def_Atlas_Core_Basic
import Definitions.Def_Atlas_Core_Lift
import Definitions.Def_Atlas_Schwarzschild_Defs
import Definitions.Def_Atlas_Schwarzschild_Domain
import Definitions.Def_Atlas_Schwarzschild_PGDefs
open Real
open scoped ContDiff

theorem ExactVacuumAtlas.Schwarzschild.PG.hasDerivAt_qf {M r : ℝ} (hM : 0 ≤ M) (hr : 0 < r) :
    HasDerivAt (fun u => qf M u) (-(qf M r) / (2 * r)) r := by sorry
