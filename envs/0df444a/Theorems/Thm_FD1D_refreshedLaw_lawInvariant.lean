-- Prove2me | Theorems.Thm_FD1D_refreshedLaw_lawInvariant
-- name    : FD1D.refreshedLaw_lawInvariant
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:05:48.896391+00:00
-- url     : https://prove2.me/theorems/d52ef9c1-ee48-4dde-b9a9-54507621504d
-- title:
--   FD1 D: refreshed Law law Invariant
-- statement:
--   The refreshed law is invariant under the canonical lift of every leaf
--   permutation to inventory states.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Initialization.lean#L162-L167
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Initialization.lean#L162-L167

import Definitions.Def_FD1D_Markov
import Definitions.Def_FD1D_Tree
import Definitions.Def_FD1D_Initialization
set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators

theorem FD1D.refreshedLaw_lawInvariant {L m : ℕ}
    (leafPerm : Equiv.Perm (DyadicNode L)) :
    FiniteKernel.LawInvariant (refreshedLaw L m)
      (inventoryStatePerm leafPerm) := by sorry
