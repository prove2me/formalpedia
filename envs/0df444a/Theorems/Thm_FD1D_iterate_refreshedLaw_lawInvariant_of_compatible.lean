-- Prove2me | Theorems.Thm_FD1D_iterate_refreshedLaw_lawInvariant_of_compatible
-- name    : FD1D.iterate_refreshedLaw_lawInvariant_of_compatible
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:42:25.805945+00:00
-- url     : https://prove2.me/theorems/e50ed265-5099-57af-8056-5925eec65fc4
-- title:
--   FD1 D: iterate refreshed Law law Invariant of compatible
-- statement:
--   Kernel equivariance preserves refreshed-law invariance through every
--   iterate, for any compatible state-space lift.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Initialization.lean#L171-L181
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Initialization.lean#L171-L181

import Definitions.Def_FD1D_Markov
import Definitions.Def_FD1D_Tree
import Definitions.Def_FD1D_Initialization
set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators

theorem FD1D.iterate_refreshedLaw_lawInvariant_of_compatible
    {L m : ℕ} (K : FiniteKernel (InventoryState (DyadicNode L) m))
    (leafPerm : Equiv.Perm (DyadicNode L))
    (statePerm : Equiv.Perm (InventoryState (DyadicNode L) m))
    (hcompat : ∀ ω : DyadicAssignment L m,
      assignmentState (assignmentPerm leafPerm ω) =
        statePerm (assignmentState ω))
    (hK : K.Equivariant statePerm) (n : ℕ) :
    FiniteKernel.LawInvariant (K.iterate n (refreshedLaw L m)) statePerm := by sorry
