-- Prove2me | Theorems.Thm_BKAR_Forest_sum_rootBoundarySupportOrderContribution_nil
-- name    : BKAR.Forest.sum_rootBoundarySupportOrderContribution_nil
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T09:19:24.050349+00:00
-- url     : https://prove2.me/theorems/b1b67576-31e4-4ab7-8426-e3bfac0aaa72
-- title:
--   Forest: sum root Boundary Support Order Contribution nil
-- statement:
--   The empty support sector sums to the ordered contribution of the empty forest.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesFiberBridge/LowRank.lean#L31-L52
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesFiberBridge/LowRank.lean#L31-L52

import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFiberBridge_Core
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFiberBridge_LowRank
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.sum_rootBoundarySupportOrderContribution_nil
    (choices : ActiveExtensionChoice V)
    (ρ : (Edge V → ℝ) → ℝ) :
    Finset.sum (Finset.univ : Finset (ForestIndex V))
        (fun I => rootBoundarySupportOrderContribution choices ρ I []) =
      (Forest.empty V).orderedContribution [] ρ := by sorry
