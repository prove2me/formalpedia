-- Prove2me | Theorems.Thm_BKAR_Forest_firstRecursiveBoundaryRemainder_eq_localRecursiveBoundaryRemainder_empty
-- name    : BKAR.Forest.firstRecursiveBoundaryRemainder_eq_localRecursiveBoundaryRemainder_empty
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T09:47:34.673413+00:00
-- url     : https://prove2.me/theorems/2c64928b-325d-4c74-bbdd-45b953d60895
-- title:
--   Forest: first Recursive Boundary Remainder eq local Recursive Boundary Remainder empty
-- statement:
--   The root recursive remainder is the empty-node instance of the local one.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesTelescoping.lean#L343-L348
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesTelescoping.lean#L343-L348

import Definitions.Def_BKAR_OrderedAssembly_AllBranchesRegrouping
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesTelescoping
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.firstRecursiveBoundaryRemainder_eq_localRecursiveBoundaryRemainder_empty
    (choices : ActiveExtensionChoice V)
    (ρ : (Edge V → ℝ) → ℝ) :
    firstRecursiveBoundaryRemainder choices ρ =
      localRecursiveBoundaryRemainder choices (Forest.empty V) [] [] 1 ρ := by sorry
