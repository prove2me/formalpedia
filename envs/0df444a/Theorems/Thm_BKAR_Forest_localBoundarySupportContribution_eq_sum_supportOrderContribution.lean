-- Prove2me | Theorems.Thm_BKAR_Forest_localBoundarySupportContribution_eq_sum_supportOrderContribution
-- name    : BKAR.Forest.localBoundarySupportContribution_eq_sum_supportOrderContribution
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:15:08.077078+00:00
-- url     : https://prove2.me/theorems/688f619c-0b57-514d-989c-5071d7353814
-- title:
--   Forest: local Boundary Support Contribution eq sum support Order Contribution
-- statement:
--   A local support fiber splits by canonical child order.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesRegrouping.lean#L214-L271
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesRegrouping.lean#L214-L271

import Definitions.Def_BKAR_OrderedAssembly_AllBranches
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesRegrouping
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.localBoundarySupportContribution_eq_sum_supportOrderContribution
    (choices : ActiveExtensionChoice V)
    (F : Forest V) (pref : List (Edge V)) (prefixTs : List ℝ)
    (top : ℝ)
    (hpref : pref.toFinset = F.edges) (hnodup : pref.Nodup)
    (I : ForestIndex V) (ρ : (Edge V → ℝ) → ℝ) :
    localBoundarySupportContribution choices F pref prefixTs top I ρ =
      Finset.sum (edgeSetOrders I.edges)
        (fun order =>
          localBoundarySupportOrderContribution choices F pref prefixTs top
            I order ρ) := by sorry
