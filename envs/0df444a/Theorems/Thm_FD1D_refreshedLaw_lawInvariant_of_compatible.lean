-- Prove2me | Theorems.Thm_FD1D_refreshedLaw_lawInvariant_of_compatible
-- name    : FD1D.refreshedLaw_lawInvariant_of_compatible
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:05:21.711258+00:00
-- url     : https://prove2.me/theorems/4f1772a8-e254-4312-9775-03cf807a340e
-- title:
--   FD1 D: refreshed Law law Invariant of compatible
-- statement:
--   A form parameterized by the target-state permutation, for clients that
--   already define their own lift of a leaf permutation.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Initialization.lean#L150-L158
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Initialization.lean#L150-L158

import Definitions.Def_FD1D_Markov
import Definitions.Def_FD1D_Tree
import Definitions.Def_FD1D_Initialization
set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators

theorem FD1D.refreshedLaw_lawInvariant_of_compatible
    {L m : ℕ} (leafPerm : Equiv.Perm (DyadicNode L))
    (statePerm : Equiv.Perm (InventoryState (DyadicNode L) m))
    (hcompat : ∀ ω : DyadicAssignment L m,
      assignmentState (assignmentPerm leafPerm ω) =
        statePerm (assignmentState ω)) :
    FiniteKernel.LawInvariant (refreshedLaw L m) statePerm := by sorry
