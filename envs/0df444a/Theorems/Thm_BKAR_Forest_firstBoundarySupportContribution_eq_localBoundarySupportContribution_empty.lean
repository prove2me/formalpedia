-- Prove2me | Theorems.Thm_BKAR_Forest_firstBoundarySupportContribution_eq_localBoundarySupportContribution_empty
-- name    : BKAR.Forest.firstBoundarySupportContribution_eq_localBoundarySupportContribution_empty
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T09:46:21.658825+00:00
-- url     : https://prove2.me/theorems/bcac2fef-ae5b-5323-b728-1dc0c7aad100
-- title:
--   Forest: first Boundary Support Contribution eq local Boundary Support Contribution empty
-- statement:
--   The root support fiber is the empty-prefix instance of the local API.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesRegrouping.lean#L357-L367
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesRegrouping.lean#L357-L367

import Definitions.Def_BKAR_OrderedAssembly_AllBranches
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesRegrouping
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.firstBoundarySupportContribution_eq_localBoundarySupportContribution_empty
    (choices : ActiveExtensionChoice V)
    (I : ForestIndex V) (ρ : (Edge V → ℝ) → ℝ) :
    firstBoundarySupportContribution choices I ρ =
      localBoundarySupportContribution choices (Forest.empty V) [] [] 1 I ρ := by sorry
