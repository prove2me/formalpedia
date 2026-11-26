-- Prove2me | Theorems.Thm_BKAR_Forest_firstBoundarySupportContribution_eq_sum_supportOrderContribution
-- name    : BKAR.Forest.firstBoundarySupportContribution_eq_sum_supportOrderContribution
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:15:47.062323+00:00
-- url     : https://prove2.me/theorems/070dfc08-4ab3-4f78-b185-77a37401c914
-- title:
--   Forest: first Boundary Support Contribution eq sum support Order Contribution
-- statement:
--   A support fiber of exposed first sectors splits by canonical edge order.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesRegrouping.lean#L415-L463
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesRegrouping.lean#L415-L463

import Definitions.Def_BKAR_OrderedAssembly_AllBranches
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesRegrouping
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.firstBoundarySupportContribution_eq_sum_supportOrderContribution
    (choices : ActiveExtensionChoice V)
    (I : ForestIndex V) (ρ : (Edge V → ℝ) → ℝ) :
    firstBoundarySupportContribution choices I ρ =
      Finset.sum (edgeSetOrders I.edges)
        (fun order =>
          firstBoundarySupportOrderContribution choices I order ρ) := by sorry
