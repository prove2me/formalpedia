-- Prove2me | Theorems.Thm_BKAR_Forest_sum_rootBoundarySupportOrderContribution_emptySupport
-- name    : BKAR.Forest.sum_rootBoundarySupportOrderContribution_emptySupport
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:57:14.694972+00:00
-- url     : https://prove2.me/theorems/05fd2531-e267-4e74-b0fc-2361ffa766ad
-- title:
--   Forest: sum root Boundary Support Order Contribution empty Support
-- statement:
--   The empty support inner sum is the empty forest ordered contribution.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesFiberBridge/LowRank.lean#L189-L201
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesFiberBridge/LowRank.lean#L189-L201

import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFiberBridge_Core
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFiberBridge_LowRank
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.sum_rootBoundarySupportOrderContribution_emptySupport
    (choices : ActiveExtensionChoice V)
    (ρ : (Edge V → ℝ) → ℝ) :
    Finset.sum (edgeSetOrders (Forest.empty V).support.edges)
        (fun order =>
          rootBoundarySupportOrderContribution choices ρ
            (Forest.empty V).support order) =
      (Forest.empty V).orderedContribution [] ρ := by sorry
