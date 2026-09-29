-- Prove2me | Theorems.Thm_Chou_residuallyFinite_freeGroup
-- name    : Chou.residuallyFinite_freeGroup
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-19T12:06:18.721473+00:00
-- url     : https://prove2.me/theorems/ace25a2e-b8f0-49f4-80be-5585faa12e8f
-- title:
--   Free groups are residually finite (external)
-- statement:
--   Every free group is residually finite: for every nontrivial element there is a
--   homomorphism to a finite group not killing it.
-- source:
--   Chou, C., Elementary amenable groups, Illinois Journal of Mathematics 24 (1980) 396–407, https://doi.org/10.1215/ijm/1256047608, p. 406 ("each free group has property (P) since it is residually finite")

import Mathlib

namespace Chou

/-- p. 406 (external): free groups are residually finite. -/
theorem residuallyFinite_freeGroup (α : Type*) : Group.ResiduallyFinite (FreeGroup α) := by
  sorry

end Chou
