-- Prove2me | Theorems.Thm_FD1D_iterate_refreshedLaw_lawInvariant
-- name    : FD1D.iterate_refreshedLaw_lawInvariant
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:43:02.240346+00:00
-- url     : https://prove2.me/theorems/0c0add67-7d1b-4652-aeb5-12fd0cf7c64b
-- title:
--   FD1 D: iterate refreshed Law law Invariant
-- statement:
--   If a kernel is equivariant under the canonical lift of a leaf
--   permutation, every iterate from the refreshed law remains invariant.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Initialization.lean#L185-L192
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Initialization.lean#L185-L192

import Definitions.Def_FD1D_Markov
import Definitions.Def_FD1D_Tree
import Definitions.Def_FD1D_Initialization
set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators

theorem FD1D.iterate_refreshedLaw_lawInvariant
    {L m : ℕ} (K : FiniteKernel (InventoryState (DyadicNode L) m))
    (leafPerm : Equiv.Perm (DyadicNode L))
    (hK : K.Equivariant (inventoryStatePerm leafPerm)) (n : ℕ) :
    FiniteKernel.LawInvariant (K.iterate n (refreshedLaw L m))
      (inventoryStatePerm leafPerm) := by sorry
