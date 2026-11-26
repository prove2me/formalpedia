-- Prove2me | Theorems.Thm_BKAR_Forest_firstBoundarySupportOrderContribution_eq_localBoundarySupportOrderContribution_empty
-- name    : BKAR.Forest.firstBoundarySupportOrderContribution_eq_localBoundarySupportOrderContribution_empty
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T09:46:37.356851+00:00
-- url     : https://prove2.me/theorems/e3d6645d-1dbc-45a6-b55f-b7c3358bd77f
-- title:
--   Forest: first Boundary Support Order Contribution eq local Boundary Support Order Contribution empty
-- statement:
--   The root support/order fiber is the empty-prefix instance of the local API.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesRegrouping.lean#L370-L383
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesRegrouping.lean#L370-L383

import Definitions.Def_BKAR_OrderedAssembly_AllBranches
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesRegrouping
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.firstBoundarySupportOrderContribution_eq_localBoundarySupportOrderContribution_empty
    (choices : ActiveExtensionChoice V)
    (I : ForestIndex V) (order : List (Edge V))
    (ρ : (Edge V → ℝ) → ℝ) :
    firstBoundarySupportOrderContribution choices I order ρ =
      localBoundarySupportOrderContribution choices (Forest.empty V) [] [] 1
        I order ρ := by sorry
